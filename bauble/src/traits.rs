use std::{borrow::Cow, collections::HashMap, fmt::Display};

use crate::{
    CustomError, SpannedValue, UnspannedVal, Val, Value,
    context::BaubleContext,
    error::{BaubleError, ErrorMsg, Level},
    path::{TypePath, TypePathElem},
    spanned::{Span, Spanned},
    types::{self, Extra, FieldType, TypeId},
    value::{Ident, PrimitiveValue},
};

/// Represents the different kinds of variants on an enum, where `Path` is a unit variant.
#[allow(missing_docs)]
#[derive(Clone, Debug, PartialEq)]
pub enum VariantKind {
    Struct,
    Tuple,
    Path,
}

impl Display for VariantKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use VariantKind::*;

        match self {
            Struct => write!(f, "struct"),
            Tuple => write!(f, "tuple"),
            Path => write!(f, "path"),
        }
    }
}

/// The error that `Bauble::from_bauble` returns.
pub struct ToRustError(Box<InnerToRustError>);

impl ToRustError {
    /// When in a `Bauble::from_bauble` function prefer using `Bauble::error`.
    pub fn new(
        in_type: std::any::TypeId,
        value_span: Span,
        kind: impl Into<ToRustErrorKind>,
    ) -> Self {
        Self(Box::new(InnerToRustError {
            in_type,
            value_span,
            kind: kind.into(),
        }))
    }
}

struct InnerToRustError {
    in_type: std::any::TypeId,
    value_span: Span,
    kind: ToRustErrorKind,
}

/// An error that occures during conversion from bauble to rust, represented as a Rust enum.
#[allow(missing_docs)]
#[derive(Debug, Clone, PartialEq)]
pub enum ToRustErrorKind {
    MissingField {
        field: String,
    },
    WrongTupleLength {
        expected: usize,
        found: usize,
    },
    WrongArrayLength {
        expected: usize,
        found: usize,
    },
    UnknownVariant {
        variant: Ident,
    },
    WrongType {
        found: Spanned<TypeId>,
    },
    WrongVariantType {
        variant: TypePathElem,
        found: TypeId,
    },
    MissingAttribute {
        attribute: String,
        attributes_span: Span,
    },
    InvalidIntLiteral {
        conv_error: rust_decimal::Error,
    },
    Custom(CustomError),
}

impl From<CustomError> for ToRustErrorKind {
    fn from(value: CustomError) -> Self {
        Self::Custom(value)
    }
}

impl BaubleError for ToRustError {
    fn level(&self) -> Level {
        match &self.0.kind {
            ToRustErrorKind::Custom(custom_error) => custom_error.level,
            _ => Level::Error,
        }
    }
    fn msg_general(&self, ctx: &BaubleContext) -> ErrorMsg {
        let types = ctx.type_registry();
        let ty = match types.get_type_by_id(self.0.in_type) {
            Some(ty) => ty.meta.path.borrow(),
            None => TypePath::new("<unregistered type>").unwrap(),
        };

        let msg = match &self.0.kind {
            ToRustErrorKind::MissingField { .. } => {
                format!("Missing field for the type {ty}")
            }
            ToRustErrorKind::WrongTupleLength { .. } => {
                format!("Wrong tuple length for the type {ty}")
            }
            ToRustErrorKind::WrongArrayLength { .. } => {
                format!("Wrong array length for the type {ty}")
            }
            ToRustErrorKind::UnknownVariant { .. } => {
                format!("Unknown variant for the type {ty}")
            }
            ToRustErrorKind::WrongType { .. } => {
                format!("Wrong kind for the type {ty}")
            }
            ToRustErrorKind::WrongVariantType { variant, .. } => {
                format!("Wrong kind for the variant {variant} of type {ty}")
            }
            ToRustErrorKind::MissingAttribute { .. } => {
                format!("Missing attribute for the type {ty}")
            }
            ToRustErrorKind::InvalidIntLiteral { conv_error } => {
                format!("Invalid integer literal of type {ty}: {conv_error}")
            }
            ToRustErrorKind::Custom(custom) => {
                format!("error for type {ty}: {}", custom.message)
            }
        };

        Spanned::new(self.0.value_span, Cow::Owned(msg))
    }

    fn msgs_specific(&self, ctx: &BaubleContext) -> Vec<(ErrorMsg, Level)> {
        let types = ctx.type_registry();
        let ty = match types.get_type_by_id(self.0.in_type) {
            Some(ty) => ty.meta.path.borrow(),
            None => TypePath::new("<unregistered type>").unwrap(),
        };

        let value_span = self.0.value_span;
        match &self.0.kind {
            ToRustErrorKind::MissingField { field, .. } => {
                vec![(
                    Spanned::new(
                        self.0.value_span,
                        Cow::Owned(format!("Missing the field {field}")),
                    ),
                    Level::Error,
                )]
            }
            ToRustErrorKind::WrongTupleLength {
                expected, found, ..
            }
            | ToRustErrorKind::WrongArrayLength {
                expected, found, ..
            } => {
                vec![(
                    Spanned::new(
                        value_span,
                        Cow::Owned(format!(
                            "Expected the length {expected}, found length {found}."
                        )),
                    ),
                    Level::Error,
                )]
            }
            ToRustErrorKind::UnknownVariant { variant, .. } => {
                vec![(
                    Spanned::new(variant.span, Cow::Borrowed("Unknown variant")),
                    Level::Error,
                )]
            }
            ToRustErrorKind::WrongType { found } => {
                vec![(
                    Spanned::new(
                        found.span,
                        Cow::Owned(format!(
                            "Expected the type {ty}, found {}",
                            types.key_type(found.value).meta.path
                        )),
                    ),
                    Level::Error,
                )]
            }
            ToRustErrorKind::WrongVariantType { variant, found } => {
                vec![(
                    Spanned::new(
                        value_span,
                        Cow::Owned(format!(
                            "Expected the variant {variant} of {ty}, found {}",
                            types.key_type(*found).meta.path
                        )),
                    ),
                    Level::Error,
                )]
            }
            ToRustErrorKind::MissingAttribute {
                attribute,
                attributes_span,
                ..
            } => {
                vec![(
                    Spanned::new(
                        *attributes_span,
                        Cow::Owned(format!("Missing the attribute `{attribute}`")),
                    ),
                    Level::Error,
                )]
            }
            ToRustErrorKind::InvalidIntLiteral { conv_error } => vec![(
                Spanned::new(
                    value_span,
                    Cow::Owned(format!(
                        "Expected a valid literal of type {ty}, but got invalid literal with error: {conv_error}"
                    )),
                ),
                Level::Error,
            )],
            ToRustErrorKind::Custom(custom_error) => custom_error.labels.clone(),
        }
    }
}

// TODO Maybe `unsafe trait`?
/// Used by bauble to abstract allocating various types.
pub trait BaubleAllocator<'a> {
    // TODO(@docs)
    #[allow(missing_docs)]
    type Out<T>
    where
        Self: 'a;

    /// The inner representation of a type path created by this allocator.
    type TypePathInner: 'static;

    /// # Safety
    /// Allocations in `value` have to be allocated with this allocator
    unsafe fn wrap<T>(&self, value: T) -> Self::Out<T>;
    /// # Safety
    /// If validated an item must be placed within the same allocator.
    unsafe fn validate<T>(&self, value: Self::Out<T>) -> Result<T, ToRustError>;

    /// Create a type path from this allocator.
    fn wrap_type_path(&self, path: TypePath) -> Self::Out<TypePath<Self::TypePathInner>>;
}

/// The standard Rust allocator when used by Bauble.
pub struct DefaultAllocator;

impl BaubleAllocator<'_> for DefaultAllocator {
    type Out<T> = T;
    type TypePathInner = String;

    unsafe fn wrap<T>(&self, value: T) -> Self::Out<T> {
        value
    }

    unsafe fn validate<T>(&self, value: Self::Out<T>) -> Result<T, ToRustError> {
        Ok(value)
    }

    fn wrap_type_path(&self, path: TypePath) -> TypePath<Self::TypePathInner> {
        path
    }
}

/// The trait used by types usable by Bauble. Any type that can be parsed by bauble should implement this trait.
pub trait Bauble<'a, A: BaubleAllocator<'a> = DefaultAllocator>: Sized + 'static {
    /// # DON'T CALL THIS, call `TypeRegistry::get_or_register_type` instead.
    ///
    /// Constructs a builtin type. A builtin type is a type which is not constructed by Bauble during loading
    /// of objects and might warrant additional rules.
    fn builtin(#[expect(unused)] registry: &mut types::TypeRegistry) -> Option<TypeId> {
        None
    }

    /// # DON'T CALL THIS, call `TypeRegistry::get_or_register_type` instead.
    ///
    /// Constructs a reflection type that bauble uses to parse and resolve types.
    fn construct_type(registry: &mut types::TypeRegistry) -> types::Type;

    /// Construct this type from a bauble value. This function doesn't do any type checking.
    fn from_bauble(val: Val, allocator: &A) -> Result<A::Out<Self>, ToRustError>;

    #[allow(missing_docs)]
    fn error(span: crate::Span, error: impl Into<ToRustErrorKind>) -> ToRustError {
        ToRustError(Box::new(InnerToRustError {
            in_type: std::any::TypeId::of::<Self>(),
            value_span: span,
            kind: error.into(),
        }))
    }
}

impl<'a, A: BaubleAllocator<'a>> Bauble<'a, A> for Val {
    fn construct_type(_: &mut types::TypeRegistry) -> types::Type {
        types::Type {
            meta: types::TypeMeta {
                path: TypePath::new("bauble::Val").unwrap().to_owned(),
                attributes: types::NamedFields::any(),
                default: Some(|_, _, _| UnspannedVal::new(Value::default())),
                ..Default::default()
            },
            kind: types::TypeKind::Primitive(types::Primitive::Any),
        }
    }

    fn from_bauble(val: Val, allocator: &A) -> Result<A::Out<Self>, ToRustError> {
        // SAFETY: no allocations are made in this method
        Ok(unsafe { allocator.wrap(val) })
    }
}

macro_rules! impl_ints {
    ($($ty:ty)*) => {
        $(
            impl<'a, A: BaubleAllocator<'a>> Bauble<'a, A> for $ty {
                fn construct_type(_: &mut types::TypeRegistry) -> types::Type {
                    types::Type {
                        meta: types::TypeMeta {
                            path: TypePath::new(stringify!($ty)).unwrap().to_owned(),
                            extra_validation: Some(|val, _registry| {
                                if let Value::Primitive(PrimitiveValue::Num(num)) = val.value.value {
                                    if !num.is_integer() {
                                        Err(
                                            crate::CustomError::new(format!("`{}` should be an integer", stringify!($ty)))
                                                .with_err_label(
                                                    Spanned::new(val.value.span, "This is a decimal number"),
                                                ),
                                        )?
                                    }

                                    if !(rust_decimal::Decimal::from(<$ty>::MIN)..=rust_decimal::Decimal::from(<$ty>::MAX)).contains(&num) {
                                        Err(
                                            crate::CustomError::new(format!("Out of range for integer `{}`", stringify!($ty)))
                                                .with_err_label(
                                                    Spanned::new(
                                                        val.value.span,
                                                        format!("Expected this to be in the range {}..={}", <$ty>::MIN, <$ty>::MAX),
                                                    ),
                                                ),
                                        )?
                                    }
                                }

                                Ok(())
                            }),
                            extra: Extra::from_iter([
                                ("min".to_string(), <$ty>::MIN.to_string()),
                                ("max".to_string(), <$ty>::MAX.to_string()),
                                ("step".to_string(), "1".to_string()),
                            ]),
                            ..Default::default()
                        },
                        kind: types::TypeKind::Primitive(types::Primitive::Num),
                    }
                }

                fn from_bauble(
                    val: Val,
                    allocator: &A,
                ) -> Result<A::Out<Self>, ToRustError> {
                    if let Value::Primitive(PrimitiveValue::Num(num)) = val.value.value {
                        num.trunc().try_into().map_err(|e| {
                            <Self as Bauble<'a, A>>::error(val.span(), ToRustErrorKind::InvalidIntLiteral { conv_error: e })
                        }).map(|value|
                            // SAFETY: no allocations are made in this method
                            unsafe { allocator.wrap(value) }
                        )
                    } else {
                        Err(<Self as Bauble<'a, A>>::error(val.span(), ToRustErrorKind::WrongType { found: val.ty }))
                    }
                }
            }
        )*
    };
}

macro_rules! impl_floats {
    ($($ty:ty)*) => {
        $(
            impl<'a, A: BaubleAllocator<'a>> Bauble<'a, A> for $ty {
                fn construct_type(_: &mut types::TypeRegistry) -> types::Type {
                    types::Type {
                        meta: types::TypeMeta {
                            path: TypePath::new(stringify!($ty)).unwrap().to_owned(),
                            ..Default::default()
                        },
                        kind: types::TypeKind::Primitive(types::Primitive::Num),
                    }
                }

                fn from_bauble(
                    val: Val,
                    allocator: &A,
                ) -> Result<A::Out<Self>, ToRustError> {
                    if let Value::Primitive(PrimitiveValue::Num(num)) = val.value.value {
                        // NOTE: This implementation always returns `Some` so we don't need any extra validation.
                        let f = <$ty>::try_from(num).expect("`Decimal `try_into` a float should always be `Some`.");
                        // SAFETY: no allocations are made in this method
                        Ok(unsafe { allocator.wrap(f) })
                    } else {
                        Err(<Self as Bauble<'a, A>>::error(val.span(), ToRustErrorKind::WrongType { found: val.ty }))
                    }
                }
            }
        )*
    };
}

impl_ints!(
    u8 u16 u32 u64 u128 usize
    i8 i16 i32 i64 i128 isize
);

impl_floats!(
    f32 f64
);

impl<'a, A: BaubleAllocator<'a>> Bauble<'a, A> for bool {
    fn construct_type(_: &mut types::TypeRegistry) -> types::Type {
        types::Type {
            meta: types::TypeMeta {
                path: TypePath::new("bool").unwrap().to_owned(),
                ..Default::default()
            },
            kind: types::TypeKind::Primitive(types::Primitive::Bool),
        }
    }

    fn from_bauble(val: Val, allocator: &A) -> Result<A::Out<Self>, ToRustError> {
        if let Value::Primitive(PrimitiveValue::Bool(b)) = val.value.value {
            // SAFETY: no allocations are made in this method
            Ok(unsafe { allocator.wrap(b) })
        } else {
            Err(<Self as Bauble<'a, A>>::error(
                val.span(),
                ToRustErrorKind::WrongType { found: val.ty },
            ))
        }
    }
}

impl Bauble<'_> for String {
    fn construct_type(_: &mut types::TypeRegistry) -> types::Type {
        types::Type {
            meta: types::TypeMeta {
                path: TypePath::new("std::String").unwrap().to_owned(),
                ..Default::default()
            },
            kind: types::TypeKind::Primitive(types::Primitive::Str),
        }
    }

    fn from_bauble(
        val: Val,
        _: &DefaultAllocator,
    ) -> Result<<DefaultAllocator as BaubleAllocator>::Out<Self>, ToRustError> {
        if let Value::Primitive(PrimitiveValue::Str(str)) = val.value.value {
            Ok(str)
        } else {
            Err(Self::error(
                val.span(),
                ToRustErrorKind::WrongType { found: val.ty },
            ))
        }
    }
}

impl<'a, A: BaubleAllocator<'a>> Bauble<'a, A> for () {
    fn construct_type(_: &mut types::TypeRegistry) -> types::Type {
        types::Type {
            meta: types::TypeMeta {
                path: TypePath::new("()").unwrap().to_owned(),
                ..Default::default()
            },
            kind: types::TypeKind::Primitive(types::Primitive::Unit),
        }
    }

    fn from_bauble(val: Val, allocator: &A) -> Result<A::Out<Self>, ToRustError> {
        if matches!(val.value.value, Value::Primitive(PrimitiveValue::Unit)) {
            // SAFETY: no allocations are made in this method
            Ok(unsafe { allocator.wrap(()) })
        } else {
            Err(<Self as Bauble<'a, A>>::error(
                val.span(),
                ToRustErrorKind::WrongType { found: val.ty },
            ))
        }
    }
}

macro_rules! impl_tuple {
    () => {};
    (impl $ident:ident) => {};
    (impl $($ident:ident)+) => {
        impl<'a, A: BaubleAllocator<'a>, $($ident: Bauble<'a, A>),+> Bauble<'a, A> for ($($ident),+) {
            fn construct_type(registry: &mut types::TypeRegistry) -> types::Type {
                let inner = [$($ident::construct_type(registry)),+];
                let inner_string = inner.iter().map(|ty| ty.meta.path.to_string()).reduce(
                    |a, b| format!("{a}, {b}")
                ).unwrap_or(",".to_string());
                let inner_string = format!("({inner_string})");
                types::Type {
                    meta: types::TypeMeta {
                        path: TypePath::new(&inner_string).unwrap().to_owned(),
                        ..Default::default()
                    },
                    kind: types::TypeKind::Tuple(
                        types::UnnamedFields::default().with_required([
                            $(
                                FieldType::from(registry.get_or_register_type::<$ident, A>())
                            ),+
                        ]),
                    ),
                }
            }

            fn from_bauble(
                val: Val,
                allocator: &A,
            ) -> Result<A::Out<Self>, ToRustError> {
                const LEN: usize = [$(stringify!($ident)),+].len();

                let span = val.span();
                if let Value::Tuple(mut seq) = val.value.value {
                    if seq.len() != LEN {
                        return Err(Self::error(span, ToRustErrorKind::WrongTupleLength {
                                expected: LEN,
                                found: seq.len(),
                            },
                        ))
                    }
                    let mut drain = seq.drain(..);
                    // SAFETY: allocator is passed to `from_bauble` so validating each element of the tuple will only have
                    // allocation made by `allocator`.
                    Ok(unsafe {
                        allocator.wrap(($(allocator.validate($ident::from_bauble(drain.next().unwrap(), allocator)?)?),+))
                    })
                } else {
                    Err(Self::error(val.span(), ToRustErrorKind::WrongType { found: val.ty }))
                }
            }
        }
    };
    ($head:ident $($tail:ident)*) => {
        impl_tuple!($($tail)*);
        impl_tuple!(impl $head $($tail)*);
    };
}

impl_tuple!(T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15);

impl<'a, A: BaubleAllocator<'a>, T: Bauble<'a, A>, const N: usize> Bauble<'a, A> for [T; N] {
    fn construct_type(registry: &mut types::TypeRegistry) -> types::Type {
        let inner = registry.get_or_register_type::<T, A>();

        types::Type {
            meta: types::TypeMeta {
                path: TypePath::new(&format!(
                    "[{}; {N}]",
                    registry.key_type(inner).meta.path.as_str(),
                ))
                .unwrap()
                .to_owned(),
                ..Default::default()
            },
            kind: types::TypeKind::Array(types::ArrayType {
                ty: FieldType::from(inner),
                len: Some(N),
            }),
        }
    }

    fn from_bauble(val: Val, allocator: &A) -> Result<A::Out<Self>, ToRustError> {
        let span = val.span();
        if let Value::Array(array) = val.value.value {
            if array.len() != N {
                return Err(Self::error(
                    span,
                    ToRustErrorKind::WrongArrayLength {
                        expected: N,
                        found: array.len(),
                    },
                ));
            }

            array
                .into_iter()
                // SAFETY: allocator is passed to from_bauble so all allocation should happen through it.
                .map(|field| unsafe {allocator.validate(T::from_bauble(field, allocator)?) })
                .try_collect::<Vec<_>>()
                // SAFETY: all allocations for each element is handled by allocator, the array itself is not allocated. 
                .map(|vec| unsafe {
                    allocator.wrap(
                        vec.try_into()
                            .unwrap_or_else(
                                |_| panic!("this should be infallible as the length of the vector should be equivalent to the length of the array due to the above check"
                            ))
                    )
                })
        } else {
            Err(Self::error(
                val.span(),
                ToRustErrorKind::WrongType { found: val.ty },
            ))
        }
    }
}

impl<'a, A: BaubleAllocator<'a>, T: Bauble<'a, A>> Bauble<'a, A> for Option<T> {
    fn construct_type(registry: &mut types::TypeRegistry) -> types::Type {
        let inner = registry.get_or_register_type::<T, A>();

        let generic_path = TypePath::new("std::Option").unwrap();
        let generic = registry.get_or_register_generic_type(generic_path);

        let none = TypePathElem::new("None").unwrap();
        let variants = registry.build_enum([
            types::Variant::explicit(none, types::Fields::Unit),
            types::Variant::explicit(
                TypePathElem::new("Some").unwrap(),
                types::Fields::Unnamed(types::UnnamedFields {
                    required: vec![types::FieldType::from(inner)],
                    ..Default::default()
                }),
            ),
        ]);

        types::Type {
            meta: types::TypeMeta {
                path: TypePath::new(format!(
                    "{generic_path}<{}>",
                    registry.key_type(inner).meta.path
                ))
                .unwrap(),
                generic_base_type: Some(generic),
                default: Some(|a, registry, ty| {
                    let none = match &registry.key_type(ty).kind {
                        types::TypeKind::Enum { variants } => variants
                            .get("None")
                            .expect("We instantiated it to this above."),
                        _ => {
                            unreachable!()
                        }
                    };
                    UnspannedVal::new(Value::Enum(
                        TypePathElem::new("None").unwrap().to_owned(),
                        Box::new(
                            registry
                                .instantiate(none, a)
                                .expect("We should be able to instantiate unit fields"),
                        ),
                    ))
                }),
                ..Default::default()
            },
            kind: types::TypeKind::Enum { variants },
        }
    }

    fn from_bauble(val: Val, allocator: &A) -> Result<A::Out<Self>, ToRustError> {
        let span = val.value.span;
        let Value::Enum(variant, val) = val.value.value else {
            return Err(Self::error(
                span,
                ToRustErrorKind::WrongType { found: val.ty },
            ));
        };

        match variant.as_str() {
            "Some" => match val.value.value {
                Value::Struct(crate::FieldsKind::Unnamed(fields)) if fields.len() == 1 => {
                    let Some(inner) = fields.into_iter().next() else {
                        unreachable!()
                    };

                    // SAFETY: We pass the same allocator we validate with.
                    let inner = unsafe { allocator.validate(T::from_bauble(inner, allocator)?)? };

                    // SAFETY: We used this allocator to create `inner`.
                    Ok(unsafe { allocator.wrap(Some(inner)) })
                }
                _ => Err(Self::error(
                    val.value.span,
                    ToRustErrorKind::WrongVariantType {
                        variant: variant.value,
                        found: *val.ty,
                    },
                )),
            },
            "None" => {
                // SAFETY: `None` doesn't contain any allocations.
                Ok(unsafe { allocator.wrap(None) })
            }
            _ => Err(Self::error(
                span,
                ToRustErrorKind::UnknownVariant {
                    variant: variant.map(|s| s.to_string()),
                },
            )),
        }
    }
}

impl<'a, T: Bauble<'a>> Bauble<'a> for Vec<T> {
    fn construct_type(registry: &mut types::TypeRegistry) -> types::Type {
        let inner = registry.get_or_register_type::<T, _>();

        types::Type {
            meta: types::TypeMeta {
                path: TypePath::new(format!("std::Vec<{}>", registry.key_type(inner).meta.path))
                    .unwrap(),
                ..Default::default()
            },
            kind: types::TypeKind::Array(types::ArrayType {
                ty: types::FieldType::from(inner),
                len: None,
            }),
        }
    }

    fn from_bauble(
        val: Val,
        allocator: &DefaultAllocator,
    ) -> Result<<DefaultAllocator as BaubleAllocator>::Out<Self>, ToRustError> {
        if let Value::Array(items) = val.value.value {
            items
                .into_iter()
                .map(|val| T::from_bauble(val, allocator))
                .try_collect()
        } else {
            Err(Self::error(
                val.span(),
                ToRustErrorKind::WrongType { found: val.ty },
            ))
        }
    }
}

impl<'a, T: Bauble<'a>> Bauble<'a> for Box<T> {
    fn construct_type(registry: &mut types::TypeRegistry) -> types::Type {
        let inner = registry.get_or_register_type::<T, _>();

        types::Type {
            meta: types::TypeMeta {
                path: TypePath::new(format!("std::Box<{}>", registry.key_type(inner).meta.path))
                    .unwrap(),
                ..Default::default()
            },
            kind: types::TypeKind::Array(types::ArrayType {
                ty: types::FieldType::from(inner),
                len: None,
            }),
        }
    }

    fn from_bauble(
        val: Val,
        allocator: &DefaultAllocator,
    ) -> Result<<DefaultAllocator as BaubleAllocator>::Out<Self>, ToRustError> {
        T::from_bauble(val, allocator).map(Box::new)
    }
}

macro_rules! impl_map {
    ($path:literal => $($part:ident)::+) => {
        impl<'a, K: Bauble<'a> + Eq + std::hash::Hash, V: Bauble<'a>> Bauble<'a> for $($part)::+<K, V> {
            fn construct_type(registry: &mut types::TypeRegistry) -> types::Type {
                let key = registry.get_or_register_type::<K, _>();
                let value = registry.get_or_register_type::<V, _>();

                types::Type {
                    meta: types::TypeMeta {
                        path: TypePath::new(format!(
                            "{}<{}, {}>",
                            $path,
                            registry.key_type(key).meta.path,
                            registry.key_type(value).meta.path
                        ))
                        .unwrap(),
                        ..Default::default()
                    },
                    kind: types::TypeKind::Map(types::MapType {
                        key: FieldType::from(key),
                        value: FieldType::from(value),
                        len: None,
                    }),
                }
            }

            fn from_bauble(
                val: Val,
                allocator: &DefaultAllocator,
            ) -> Result<<DefaultAllocator as BaubleAllocator>::Out<Self>, ToRustError> {
                if let Value::Map(map) = val.value.value {
                    map.into_iter()
                        .map(|(k, v)| {
                            Ok((K::from_bauble(k, allocator)?, V::from_bauble(v, allocator)?))
                        })
                        .try_collect()
                } else {
                    Err(Self::error(
                        val.span(),
                        ToRustErrorKind::WrongType { found: val.ty },
                    ))
                }
            }
        }
    };
}

impl_map!("std::HashMap" => HashMap);

#[cfg(feature = "hashbrown")]
impl_map!("hashbrown::HashMap" => hashbrown::HashMap);

#[cfg(feature = "enumset")]
impl<'a, A: BaubleAllocator<'a>, T: Bauble<'a, A> + enumset::EnumSetType> Bauble<'a, A>
    for enumset::EnumSet<T>
{
    fn construct_type(registry: &mut types::TypeRegistry) -> types::Type {
        types::Type {
            meta: types::TypeMeta {
                path: TypePath::new("enumset").unwrap().to_owned(),
                ..Default::default()
            },
            kind: types::TypeKind::Array(types::ArrayType {
                ty: registry.get_or_register_type::<T, A>().into(),
                len: None,
            }),
        }
    }

    fn from_bauble(val: Val, allocator: &A) -> Result<A::Out<Self>, ToRustError> {
        if let Value::Array(bitflags) = val.value.value {
            let res = bitflags
                .into_iter()
                .map(|value| {
                    let value = T::from_bauble(value, allocator)?;

                    // SAFETY: no allocations are made in this method
                    unsafe { allocator.validate(value) }
                })
                .try_collect()?;

            // SAFETY: the elements were wrapped with the same allocator
            Ok(unsafe { allocator.wrap(res) })
        } else {
            Err(Self::error(
                val.span(),
                ToRustErrorKind::WrongType { found: val.ty },
            ))
        }
    }
}
