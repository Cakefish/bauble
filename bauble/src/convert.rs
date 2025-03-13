use std::{borrow::Cow, collections::HashMap, fmt::Display};

use indexmap::IndexMap;

use crate::{
    Val, Value,
    error::{BaubleError, ErrorMsg, Level},
    parse::Ident,
    path::{TypePath, TypePathElem},
    spanned::{Span, Spanned},
    types::{self, FieldType, TypeId},
    value::PrimitiveValue,
};

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

pub struct FullDeserializeError {
    in_type: std::any::TypeId,
    value_span: Span,
    kind: DeserializeError,
}

#[derive(Debug, Clone, PartialEq)]
pub enum DeserializeError {
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
        found: TypeId,
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

#[derive(Clone, Debug, PartialEq)]
pub struct CustomError {
    pub message: Cow<'static, str>,
    pub level: Level,
    pub labels: Vec<(Spanned<Cow<'static, str>>, Level)>,
}

impl CustomError {
    pub fn new(s: impl Into<Cow<'static, str>>) -> Self {
        Self {
            message: s.into(),
            level: Level::Error,
            labels: Vec::new(),
        }
    }

    pub fn with_level(mut self, level: Level) -> Self {
        self.level = level;
        self
    }

    pub fn with_label(mut self, s: Spanned<impl Into<Cow<'static, str>>>, level: Level) -> Self {
        self.labels.push((s.map(|s| s.into()), level));
        self
    }

    pub fn with_err_label(self, s: Spanned<impl Into<Cow<'static, str>>>) -> Self {
        self.with_label(s, Level::Error)
    }
}

impl BaubleError for FullDeserializeError {
    fn level(&self) -> Level {
        match &self.kind {
            DeserializeError::Custom(custom_error) => custom_error.level,
            _ => Level::Error,
        }
    }
    fn msg_general(&self, types: &types::TypeRegistry) -> ErrorMsg {
        let ty = match types.get_type_by_id(self.in_type) {
            Some(ty) => ty.meta.path.borrow(),
            None => TypePath::new("<unregistered type>").unwrap(),
        };

        let msg = match &self.kind {
            DeserializeError::MissingField { .. } => {
                format!("Missing field for the type {ty}")
            }
            DeserializeError::WrongTupleLength { .. } => {
                format!("Wrong tuple length for the type {ty}")
            }
            DeserializeError::WrongArrayLength { .. } => {
                format!("Wrong array length for the type {ty}")
            }
            DeserializeError::UnknownVariant { .. } => {
                format!("Unknown variant for the type {ty}")
            }
            DeserializeError::WrongType { .. } => {
                format!("Wrong kind for the type {ty}")
            }
            DeserializeError::WrongVariantType { variant, .. } => {
                format!("Wrong kind for the variant {variant} of type {ty}")
            }
            DeserializeError::MissingAttribute { .. } => {
                format!("Missing attributy for the type {ty}")
            }
            DeserializeError::InvalidIntLiteral { conv_error } => {
                format!("Invalid literal of type {ty}: {conv_error}")
            }
            DeserializeError::Custom(custom) => {
                format!("error for type {ty}: {}", custom.message)
            }
        };

        Spanned::new(self.value_span, Cow::Owned(msg))
    }

    fn msgs_specific(&self, types: &types::TypeRegistry) -> Vec<(ErrorMsg, Level)> {
        let ty = match types.get_type_by_id(self.in_type) {
            Some(ty) => ty.meta.path.borrow(),
            None => TypePath::new("<unregistered type>").unwrap(),
        };

        match &self.kind {
            DeserializeError::MissingField { field, .. } => {
                vec![(
                    Spanned::new(
                        self.value_span,
                        Cow::Owned(format!("Missing field the field {field}")),
                    ),
                    Level::Error,
                )]
            }
            DeserializeError::WrongTupleLength {
                expected, found, ..
            }
            | DeserializeError::WrongArrayLength {
                expected, found, ..
            } => {
                vec![(
                    Spanned::new(
                        self.value_span,
                        Cow::Owned(format!(
                            "Expected the length {expected}, found length {found}."
                        )),
                    ),
                    Level::Error,
                )]
            }
            DeserializeError::UnknownVariant { variant, .. } => {
                vec![(
                    Spanned::new(variant.span, Cow::Borrowed("Unknown variant")),
                    Level::Error,
                )]
            }
            DeserializeError::WrongType { found } => {
                vec![(
                    Spanned::new(
                        self.value_span,
                        // TODO:
                        Cow::Owned(format!(
                            "Expected the kind {ty}, found {}",
                            types.key_type(*found).meta.path
                        )),
                    ),
                    Level::Error,
                )]
            }
            DeserializeError::WrongVariantType { variant, found } => {
                vec![(
                    Spanned::new(
                        self.value_span,
                        // TODO:
                        Cow::Owned(format!(
                            "Expected the variant {variant} of {ty}, found {}",
                            types.key_type(*found).meta.path
                        )),
                    ),
                    Level::Error,
                )]
            }
            DeserializeError::MissingAttribute {
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
            DeserializeError::InvalidIntLiteral { conv_error } => vec![(
                Spanned::new(
                    self.value_span,
                    Cow::Owned(format!(
                        "Expected a valid literal of type {ty}, but got invalid literal with error: {conv_error}"
                    )),
                ),
                Level::Error,
            )],
            DeserializeError::Custom(custom_error) => custom_error.labels.clone(),
        }
    }
}

pub type FromBaubleError = Box<FullDeserializeError>;

// TODO Maybe `unsafe trait`?
pub trait BaubleAllocator<'a> {
    type Out<T>
    where
        Self: 'a;

    /// # Safety
    /// Allocations in `value` have to be allocated with this allocator
    unsafe fn wrap<T>(&self, value: T) -> Self::Out<T>;
    /// # Safety
    /// If validated an item must be placed within the same allocator.
    unsafe fn validate<T>(&self, value: Self::Out<T>) -> Result<T, FromBaubleError>;
}

pub struct DefaultAllocator;

impl BaubleAllocator<'_> for DefaultAllocator {
    type Out<T> = T;

    unsafe fn wrap<T>(&self, value: T) -> Self::Out<T> {
        value
    }

    unsafe fn validate<T>(&self, value: Self::Out<T>) -> Result<T, FromBaubleError> {
        Ok(value)
    }
}

pub trait Bauble<'a, A: BaubleAllocator<'a> = DefaultAllocator>: Sized + 'static {
    /// Constructs a reflection type that bauble uses to parse and resolve types.
    fn construct_type(registry: &mut types::TypeRegistry) -> types::Type;

    /// Construct this type from a bauble value. This function doesn't do any type checking.
    fn from_bauble(val: Val, allocator: &A) -> Result<A::Out<Self>, FromBaubleError>;

    fn error(span: crate::Span, error: DeserializeError) -> FromBaubleError {
        Box::new(FullDeserializeError {
            in_type: std::any::TypeId::of::<Self>(),
            value_span: span,
            kind: error,
        })
    }
}

impl<'a, A: BaubleAllocator<'a>> Bauble<'a, A> for Val {
    fn construct_type(_: &mut types::TypeRegistry) -> types::Type {
        types::Type {
            meta: types::TypeMeta {
                path: TypePath::new("bauble::Val").unwrap().to_owned(),
                ..Default::default()
            },
            kind: types::TypeKind::Primitive(types::Primitive::Any),
        }
    }

    fn from_bauble(val: Val, allocator: &A) -> Result<A::Out<Self>, FromBaubleError> {
        // SAFETY: no allocations are made in this method
        Ok(unsafe { allocator.wrap(val) })
    }
}

macro_rules! impl_nums {
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
                ) -> Result<A::Out<Self>, FromBaubleError> {
                    if let Value::Primitive(PrimitiveValue::Num(num)) = val.value.value {
                        num.trunc().try_into().map_err(|e| {
                            Box::new(FullDeserializeError {
                                in_type: std::any::TypeId::of::<Self>(),
                                value_span: val.span(),
                                kind: DeserializeError::InvalidIntLiteral { conv_error: e },
                            })
                        }).map(|value|
                            // SAFETY: no allocations are made in this method
                            unsafe { allocator.wrap(value) }
                        )
                    } else {
                        Err(Box::new(FullDeserializeError {
                            in_type: std::any::TypeId::of::<Self>(),
                            value_span: val.span(),
                            kind: DeserializeError::WrongType { found: val.ty },
                        }))
                    }
                }
            }
        )*
    };
}

impl_nums!(
    u8 u16 u32 u64 u128 usize
    i8 i16 i32 i64 i128 isize
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

    fn from_bauble(val: Val, allocator: &A) -> Result<A::Out<Self>, FromBaubleError> {
        if let Value::Primitive(PrimitiveValue::Bool(b)) = val.value.value {
            // SAFETY: no allocations are made in this method
            Ok(unsafe { allocator.wrap(b) })
        } else {
            Err(Box::new(FullDeserializeError {
                in_type: std::any::TypeId::of::<bool>(),
                value_span: val.span(),
                kind: DeserializeError::WrongType { found: val.ty },
            }))
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
    ) -> Result<<DefaultAllocator as BaubleAllocator>::Out<Self>, FromBaubleError> {
        if let Value::Primitive(PrimitiveValue::Str(str)) = val.value.value {
            Ok(str)
        } else {
            Err(Self::error(
                val.span(),
                DeserializeError::WrongType { found: val.ty },
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

    fn from_bauble(val: Val, allocator: &A) -> Result<A::Out<Self>, FromBaubleError> {
        if matches!(val.value.value, Value::Primitive(PrimitiveValue::Unit)) {
            // SAFETY: no allocations are made in this method
            Ok(unsafe { allocator.wrap(()) })
        } else {
            Err(Box::new(FullDeserializeError {
                in_type: std::any::TypeId::of::<Self>(),
                value_span: val.span(),
                kind: DeserializeError::WrongType { found: val.ty },
            }))
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
                let mut inner_string = inner.iter().map(|ty| ty.meta.path.as_str()).fold(
                    "".to_string(),
                    |acc, add| format!("{acc}{add},")
                );
                // remove trailing comma;
                inner_string.pop();
                let inner_string = format!("({inner_string})");
                types::Type {
                    meta: types::TypeMeta {
                        path: TypePath::new(&inner_string).unwrap().to_owned(),
                        ..Default::default()
                    },
                    kind: types::TypeKind::Tuple(
                        types::UnnamedFields::default().with_required([
                            $(
                                FieldType {
                                    id: registry.get_or_register_type::<$ident, A>(),
                                    extra: IndexMap::new(),
                                }
                            ),+
                        ]),
                    ),
                }
            }

            fn from_bauble(
                val: Val,
                allocator: &A,
            ) -> Result<A::Out<Self>, FromBaubleError> {
                const LEN: usize = [$(stringify!($ident)),+].len();

                let span = val.span();
                if let Value::Tuple(mut seq) = val.value.value {
                    if seq.len() != LEN {
                        return Err(Box::new(FullDeserializeError {
                            in_type: std::any::TypeId::of::<Self>(),
                            value_span: span,
                            kind: DeserializeError::WrongTupleLength {
                                expected: LEN,
                                found: seq.len(),
                            },
                        }))
                    }
                    let mut drain = seq.drain(..);
                    // SAFETY: allocator is passed to `from_bauble` so validating each element of the tuple will only have
                    // allocation made by `allocator`.
                    Ok(unsafe {
                        allocator.wrap(($(allocator.validate($ident::from_bauble(drain.next().unwrap(), allocator)?)?),+))
                    })
                } else {
                    Err(Self::error(val.span(), DeserializeError::WrongType { found: val.ty }))
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
        types::Type {
            meta: types::TypeMeta {
                path: TypePath::new(&format!(
                    "[{}; {}]",
                    T::construct_type(registry).meta.path.as_str(),
                    N
                ))
                .unwrap()
                .to_owned(),
                ..Default::default()
            },
            kind: types::TypeKind::Array(types::ArrayType {
                ty: FieldType {
                    id: registry.get_or_register_type::<T, A>(),
                    extra: IndexMap::new(),
                },
                len: Some(N),
            }),
        }
    }

    fn from_bauble(val: Val, allocator: &A) -> Result<A::Out<Self>, FromBaubleError> {
        let span = val.span();
        if let Value::Array(array) = val.value.value {
            if array.len() != N {
                return Err(Box::new(FullDeserializeError {
                    in_type: std::any::TypeId::of::<Self>(),
                    value_span: span,
                    kind: DeserializeError::WrongArrayLength {
                        expected: N,
                        found: array.len(),
                    },
                }));
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
                DeserializeError::WrongType { found: val.ty },
            ))
        }
    }
}

impl<'a, A: BaubleAllocator<'a>, T: Bauble<'a, A>> Bauble<'a, A> for Option<T> {
    fn construct_type(registry: &mut types::TypeRegistry) -> types::Type {
        let inner = registry.get_or_register_type::<T, A>();

        let generic_path = TypePath::new("std::Option").unwrap();
        let generic = registry.get_or_register_generic_type(generic_path);

        let kind = registry.build_enum([
            types::Variant::explicit(
                TypePathElem::new("Some").unwrap(),
                types::Fields::Unnamed(types::UnnamedFields {
                    required: vec![types::FieldType {
                        id: inner,
                        extra: Default::default(),
                    }],
                    ..Default::default()
                }),
            ),
            types::Variant::explicit(TypePathElem::new("None").unwrap(), types::Fields::Unit),
        ]);

        types::Type {
            meta: types::TypeMeta {
                path: TypePath::new(format!(
                    "{generic_path}<{}>",
                    registry.key_type(inner).meta.path
                ))
                .unwrap(),
                generic_base_type: Some(generic),
                ..Default::default()
            },
            kind,
        }
    }

    fn from_bauble(val: Val, allocator: &A) -> Result<A::Out<Self>, FromBaubleError> {
        let span = val.value.span;
        let Value::Enum(variant, val) = val.value.value else {
            return Err(Self::error(
                span,
                DeserializeError::WrongType { found: val.ty },
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
                    DeserializeError::WrongVariantType {
                        variant: variant.value,
                        found: val.ty,
                    },
                )),
            },
            "None" => {
                // SAFETY: `None` doesn't contain any allocations.
                Ok(unsafe { allocator.wrap(None) })
            }
            _ => Err(Self::error(
                span,
                DeserializeError::UnknownVariant {
                    variant: variant.map(|s| s.to_string()),
                },
            )),
        }
    }
}

impl<'a, T: Bauble<'a>> Bauble<'a> for Vec<T> {
    fn construct_type(registry: &mut types::TypeRegistry) -> types::Type {
        let inner = registry.get_or_register_type::<T, _>();

        let generic_path = TypePath::new("std::Vec").unwrap();
        let generic = registry.get_or_register_generic_type(generic_path);

        types::Type {
            meta: types::TypeMeta {
                path: TypePath::new(format!(
                    "{generic_path}<{}>",
                    registry.key_type(inner).meta.path
                ))
                .unwrap(),
                generic_base_type: Some(generic),
                ..Default::default()
            },
            kind: types::TypeKind::Array(types::ArrayType {
                ty: types::FieldType {
                    id: inner,
                    extra: Default::default(),
                },
                len: None,
            }),
        }
    }

    fn from_bauble(
        val: Val,
        allocator: &DefaultAllocator,
    ) -> Result<<DefaultAllocator as BaubleAllocator>::Out<Self>, FromBaubleError> {
        if let Value::Array(items) = val.value.value {
            items
                .into_iter()
                .map(|val| T::from_bauble(val, allocator))
                .try_collect()
        } else {
            Err(Self::error(
                val.span(),
                DeserializeError::WrongType { found: val.ty },
            ))
        }
    }
}

impl<'a, T: Bauble<'a>> Bauble<'a> for Box<T> {
    fn construct_type(registry: &mut types::TypeRegistry) -> types::Type {
        let inner = registry.get_or_register_type::<T, _>();

        let generic_path = TypePath::new("std::Box").unwrap();
        let generic = registry.get_or_register_generic_type(generic_path);

        types::Type {
            meta: types::TypeMeta {
                path: TypePath::new(format!(
                    "{generic_path}<{}>",
                    registry.key_type(inner).meta.path
                ))
                .unwrap(),
                generic_base_type: Some(generic),
                ..Default::default()
            },
            kind: types::TypeKind::Array(types::ArrayType {
                ty: types::FieldType {
                    id: inner,
                    extra: Default::default(),
                },
                len: None,
            }),
        }
    }

    fn from_bauble(
        val: Val,
        allocator: &DefaultAllocator,
    ) -> Result<<DefaultAllocator as BaubleAllocator>::Out<Self>, FromBaubleError> {
        T::from_bauble(val, allocator).map(Box::new)
    }
}

macro_rules! impl_map {
    ($path:literal => $($part:ident)::+) => {
        impl<'a, K: Bauble<'a> + Eq + std::hash::Hash, V: Bauble<'a>> Bauble<'a> for $($part)::+<K, V> {
            fn construct_type(registry: &mut types::TypeRegistry) -> types::Type {
                let key = registry.get_or_register_type::<K, _>();
                let value = registry.get_or_register_type::<V, _>();

                let generic_path = TypePath::new($path).unwrap();
                let generic = registry.get_or_register_generic_type(generic_path);

                types::Type {
                    meta: types::TypeMeta {
                        path: TypePath::new(format!(
                            "{generic_path}<{}, {}>",
                            registry.key_type(key).meta.path,
                            registry.key_type(value).meta.path
                        ))
                        .unwrap(),
                        generic_base_type: Some(generic),
                        ..Default::default()
                    },
                    kind: types::TypeKind::Map(types::MapType {
                        key: FieldType {
                            id: key,
                            extra: IndexMap::new(),
                        },
                        value: FieldType {
                            id: value,
                            extra: IndexMap::new(),
                        },
                        len: None,
                    }),
                }
            }

            fn from_bauble(
                val: Val,
                allocator: &DefaultAllocator,
            ) -> Result<<DefaultAllocator as BaubleAllocator>::Out<Self>, FromBaubleError> {
                if let Value::Map(map) = val.value.value {
                    map.into_iter()
                        .map(|(k, v)| {
                            Ok((K::from_bauble(k, allocator)?, V::from_bauble(v, allocator)?))
                        })
                        .try_collect()
                } else {
                    Err(Self::error(
                        val.span(),
                        DeserializeError::WrongType { found: val.ty },
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
                ty: FieldType {
                    id: registry.get_or_register_type::<T, A>(),
                    extra: IndexMap::new(),
                },
                len: None,
            }),
        }
    }

    fn from_bauble(val: Val, allocator: &A) -> Result<A::Out<Self>, FromBaubleError> {
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
            Err(Box::new(FullDeserializeError {
                in_type: std::any::TypeId::of::<Self>(),
                value_span: val.span(),
                kind: DeserializeError::WrongType { found: val.ty },
            }))
        }
    }
}
