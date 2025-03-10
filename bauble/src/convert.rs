use std::{borrow::Cow, fmt::Display};

use crate::{
    Val, Value,
    error::{BaubleError, ErrorMsg, Level},
    parse::Ident,
    path::{TypePath, TypePathElem},
    spanned::{Span, Spanned},
    types::{self, TypeId},
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
            DeserializeError::Custom(custom) => {
                format!("error for type {ty}: {}", custom.message)
            }
        };

        Spanned::new(self.value_span, Cow::Owned(msg))
    }

    fn msgs_specific(&self, types: &types::TypeRegistry) -> Vec<(ErrorMsg, Level)> {
        use Level::*;
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
                    Error,
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

/*
#[derive(Clone, Copy)]
pub struct FromBaubleCtx<'r, 'alloc, A: BaubleAllocator<'alloc>, Ctx: AssetContext> {
    pub allocator: &'r A,
    pub ctx: &'r Ctx,
    _marker: PhantomData<&'alloc ()>,
}

impl<'r, 'alloc, A: BaubleAllocator<'alloc>, Ctx: AssetContext> FromBaubleCtx<'r, 'alloc, A, Ctx> {
    pub fn type_id<T: Bauble<'alloc, A>>(&self, span: &Span) -> Result<TypeId, FromBaubleError> {
        self.ctx.type_registry().type_id::<T, A>().ok_or_else(|| {
            Box::new(FullDeserializeError {
                in_type: types::TypeRegistry::any_type(),
                value_span: span.clone(),
                kind: DeserializeError::UnregisteredType {
                    type_name: std::any::type_name::<T>(),
                },
            })
        })
    }
    /// Can panic if this type isn't registered.
    pub fn error<T: Bauble<'alloc, A>>(
        &self,
        span: Span,
        error: DeserializeError,
    ) -> FromBaubleError {
        match self.type_id::<T>(&span) {
            Ok(in_type) => Box::new(FullDeserializeError {
                in_type,
                value_span: span,
                kind: error,
            }),
            Err(err) => err,
        }
    }

    pub fn custom_error<T: Bauble<'alloc, A>>(
        &self,
        span: Span,
        error: CustomError,
    ) -> FromBaubleError {
        self.error::<T>(span, DeserializeError::Custom(error))
    }

    pub fn make_type_value<'a, T: Bauble<'alloc, A>>(
        &'a self,
        mut val: Val,
    ) -> Result<TypeValue<'a, 'alloc, A, Ctx, T>, FromBaubleError> {
        let id = self.type_id::<T>(&val.value.span)?;

        if self.ctx.type_registry().can_infer_from(id, val.ty) {
            return Err(Box::new(FullDeserializeError {
                in_type: id,
                value_span: val.span(),
                kind: DeserializeError::WrongType { got: val.ty },
            }));
        }

        let val_ty = self.ctx.type_registry().key_type(val.ty);

        let span = val.span();

        let mut attributes = IndexMap::new();
        let attributes_span = val.attributes.span();

        for (ident, _) in &val_ty.meta.attributes.required {
            let (key, attr) = val
                .attributes
                .0
                .shift_remove_entry(ident.as_str())
                .ok_or_else(|| {
                    self.error::<T>(
                        span.clone(),
                        DeserializeError::MissingAttribute {
                            attribute: ident.clone(),
                            attributes_span: attributes_span.clone(),
                        },
                    )
                })?;
            match attributes.insert(key, attr) {
                Some(_) => unreachable!("We're inserting from a map"),
                None => {}
            }
        }

        if val_ty.meta.attributes.allow_additional.is_some() {
            attributes.append(&mut val.attributes.0);
        } else {
            for (ident, _) in &val_ty.meta.attributes.optional {
                if let Some((key, attr)) = val.attributes.0.shift_remove_entry(ident.as_str()) {
                    match attributes.insert(key, attr) {
                        Some(_) => unreachable!("We're inserting from a map"),
                        None => {}
                    }
                }
            }
        }

        let attributes = attributes.spanned(attributes_span);

        let kind = if matches!(val_ty.kind, types::TypeKind::Transparent(_)) {
            TypeValueKind::Transparent(val)
        } else {
            match (val.value.value, &val_ty.kind) {
                (Value::Tuple(values), types::TypeKind::Tuple(ty)) => {
                    TypeValueKind::Tuple { ty, values }
                }
                (Value::Array(values), types::TypeKind::Array(ty)) => {
                    TypeValueKind::Array { ty, values }
                }
                (Value::Map(values), types::TypeKind::Map(ty)) => TypeValueKind::Map { ty, values },
                (Value::Ref(value), types::TypeKind::Ref(ty)) => TypeValueKind::Ref { ty, value },
                (Value::BitFlags(values), types::TypeKind::BitFlags(ty)) => {
                    TypeValueKind::BitFlags { ty, values }
                }
                (Value::Primitive(value), types::TypeKind::Primitive(prim)) => todo!(),

                (value, ty) => {
                    return Err(self.error::<T>(span, DeserializeError::WrongKind {}));
                }
            }
        };

        Ok(TypeValue {
            type_meta: &val_ty.meta,
            into_type: id,
            // TODO:
            variant: None,
            attributes,
            ctx: *self,
            span,
            kind,
            _marker: PhantomData,
        })
    }
}

pub enum TypeValueKind<'a> {
    Transparent(Val),
    Tuple {
        ty: &'a types::UnnamedFields,
        values: Vec<Val>,
    },
    Array {
        ty: &'a types::ArrayType,
        values: Vec<Val>,
    },
    Map {
        ty: &'a types::MapType,
        values: Vec<(Val, Val)>,
    },
    BitFlags {
        ty: &'a types::BitFlagsType,
        values: Vec<TypePathElem>,
    },
    Ref {
        ty: TypeId,
        value: TypePath,
    },
    Primitive(PrimitiveValue),
    Struct {
        ty: &'a types::Fields,
        fields: FieldValue<'a>,
    },
}

pub enum FieldValue<'a> {
    Unit,
    Unnamed {
        ty: &'a types::UnnamedFields,
        values: Vec<Val>,
    },
    Named {
        ty: &'a types::NamedFields,
        fields: crate::value::Fields,
    },
}

pub struct TypeValue<
    'r,
    'alloc,
    A: BaubleAllocator<'alloc>,
    Ctx: AssetContext,
    T: Bauble<'alloc, A>,
> {
    /// The type meta of the value.
    pub type_meta: &'r types::TypeMeta,
    /// The `TypeId` of `T`, i.e the type we're deserializing into.
    pub into_type: TypeId,
    /// If the value is an enum variant this is `Some((enum type id, variant identifier))`.
    pub variant: Option<(TypeId, TypePathElem<&'r str>)>,
    attributes: Spanned<crate::value::Fields>,
    ctx: FromBaubleCtx<'r, 'alloc, A, Ctx>,
    span: Span,
    kind: TypeValueKind<'r>,
    _marker: PhantomData<T>,
}

impl<'r, 'alloc, A: BaubleAllocator<'alloc>, Ctx: AssetContext, T: Bauble<'alloc, A>>
    TypeValue<'r, 'alloc, A, Ctx, T>
{
    pub fn span(&self) -> Span {
        self.span.clone()
    }

    pub fn take_attribute(&mut self, s: &str) -> Option<Val> {
        self.attributes.shift_remove(s)
    }

    pub fn take_required_attribute(&mut self, s: &str) -> Result<Val, FromBaubleError> {
        self.take_attribute(s).ok_or_else(|| {
            self.error(DeserializeError::MissingAttribute {
                attribute: s.to_string(),
                attributes_span: self.attributes.span(),
            })
        })
    }

    pub fn take_attributes(&mut self) -> Spanned<impl IntoIterator<Item = (Ident, Val)>> {
        let span = self.attributes.span();
        self.attributes.drain(..).spanned(span)
    }

    pub fn take_val(&mut self) -> TypeValueKind<'r> {
        std::mem::replace(
            &mut self.kind,
            TypeValueKind::Primitive(PrimitiveValue::Unit),
        )
    }

    pub fn error(&self, error: DeserializeError) -> FromBaubleError {
        self.ctx.error::<T>(self.span(), error)
    }

    pub fn custom_error(&self, error: CustomError) -> FromBaubleError {
        self.ctx.custom_error::<T>(self.span(), error)
    }

    pub fn ctx(&self) -> FromBaubleCtx<'r, 'alloc, A, Ctx> {
        self.ctx
    }
}

impl<'r, 'alloc, A: BaubleAllocator<'alloc>, Ctx: AssetContext> std::ops::Deref
    for FromBaubleCtx<'r, 'alloc, A, Ctx>
{
    type Target = A;

    fn deref(&self) -> &Self::Target {
        &self.allocator
    }
}
*/

pub trait Bauble<'a, A: BaubleAllocator<'a> = DefaultAllocator>: Sized + 'static {
    /// Constructs a reflection type that bauble uses to parse and resolve types.
    fn construct_type(registry: &mut types::TypeRegistry) -> types::Type;

    fn from_bauble(val: Val, allocator: &A) -> Result<A::Out<Self>, FromBaubleError>;

    fn error(span: crate::Span, error: DeserializeError) -> FromBaubleError {
        Box::new(FullDeserializeError {
            in_type: std::any::TypeId::of::<Self>(),
            value_span: span,
            kind: error,
        })
    }
}

impl Bauble<'_> for Val {
    fn construct_type(_: &mut types::TypeRegistry) -> types::Type {
        types::Type {
            meta: types::TypeMeta {
                path: TypePath::new("bauble::Val").unwrap().to_owned(),
                ..Default::default()
            },
            kind: types::TypeKind::Primitive(types::Primitive::Any),
        }
    }

    fn from_bauble(
        val: Val,
        _: &DefaultAllocator,
    ) -> Result<<DefaultAllocator as BaubleAllocator>::Out<Self>, FromBaubleError> {
        Ok(val)
    }
}

impl<'a, A: BaubleAllocator<'a>, T: Bauble<'a, A>> Bauble<'a, A> for Option<T> {
    fn construct_type(registry: &mut types::TypeRegistry) -> types::Type {
        let inner = registry.get_or_register_type::<T, A>();

        let generic_path = TypePath::new("std::Option").unwrap();
        let generic = registry.get_or_register_generic_type(generic_path);

        let kind = registry.build_enum([
            (
                TypePathElem::new("Some").unwrap(),
                types::Fields::Unnamed(types::UnnamedFields {
                    required: vec![types::FieldType {
                        id: inner,
                        extra: Default::default(),
                    }],
                    ..Default::default()
                }),
                types::NamedFields::default(),
            ),
            (
                TypePathElem::new("None").unwrap(),
                types::Fields::Unit,
                types::NamedFields::default(),
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
        match val.value.value {
            Value::Array(items) => items
                .into_iter()
                .map(|val| T::from_bauble(val, allocator))
                .try_collect(),
            _ => Err(Self::error(
                val.span(),
                DeserializeError::WrongType { found: val.ty },
            )),
        }
    }
}

/*
/// Match on a simple value, assumes no attributes, and only one valid Value to convert from.
#[macro_export]
macro_rules! match_val {
    ($value:expr, ($ident:ident$(($($field:ident),+))?, $span:ident) => $block:expr $(,)?) => {
        {
            let value = $value;
            if let Some((attribute, _)) = value.attributes.value.0.iter().next() {
                Err($crate::DeserializeError::new::<Self>(value.span(), $crate::DeserializeErrorKind::UnexpectedAttribute {
                    attribute: attribute.clone(),
                }))?
            }

            let $crate::Spanned { value, span } = value.value;
            Ok(match (value, span) {
                ($crate::Value::$ident $(($($field),+))?, $span) => $block,
                (value, span) => Err($crate::DeserializeError::new::<Self>(span, $crate::DeserializeErrorKind::WrongKind {
                    expected: $crate::ValueKind::$ident,
                    found: value.kind(),
                }))?,
            })
        }
    };
}

macro_rules! impl_nums {
    ($($ty:ty,)*) => {
        $(
            impl<'a, A: BaubleAllocator<'a>> Bauble<'a, A> for $ty {
                fn construct_type(_: &mut types::TypeRegistry) -> types::Type {
                    types::Type {
                        meta: types::TypeMeta {
                            path: TypePath::new(stringify!($ty)).unwrap().to_owned(),
                            ..Default::default()
                        },
                        kind: types::TypeKind::Number,
                    }
                }

                fn from_bauble(
                    val: Val,
                    allocator: &A,
                ) -> Result<A::Out<Self>, FromBaubleError> {
                    match_val!(
                        val,
                        (Num(number), span) => {
                            let number = paste::paste!(number.[< to_ $ty >]())
                                .ok_or_else(||
                                    CustomError::new("Invalid number")
                                    .with_err_label(format!("{number} is not a valid {}", stringify!($ty)).spanned(span.clone()))
                                    .error::<Self>(span))?;
                            // SAFETY: No allocations are contained in these types.
                            unsafe { allocator.wrap(number) }
                        }
                    )
                }
            }
        )*
    };
}

impl_nums! {
    u8, u16, u32, u64, u128, usize,
    i8, i16, i32, i64, i128, isize,
    f32, f64,
}

impl<'a, A: BaubleAllocator<'a>> Bauble<'a, A> for () {
    fn construct_type(_: &mut types::TypeRegistry) -> types::Type {
        types::Type {
            meta: types::TypeMeta {
                path: TypePath::new("()").unwrap().to_owned(),
                ..Default::default()
            },
            kind: types::TypeKind::Unit,
        }
    }

    fn from_bauble(val: Val, a: &A) -> Result<A::Out<Self>, FromBaubleError> {
        match_val!(
            val,
            // SAFETY: No allocations
            (Unit, _span) => unsafe { a.wrap(()) },
        )
    }
}
/*
impl<'a, T: Bauble<'a>> Bauble<'a> for Vec<T> {
    fn construct_type(registry: &mut types::TypeRegistry) -> types::Type {
        let inner = registry.get_or_register_type::<T, _>();

        let generic_path = TypePath::new("std::vec::Vec").unwrap();
        let generic = registry.get_or_register_generic_type(generic_path);

        types::Type {
            meta: types::TypeMeta {
                generic_base_type: Some(generic),
                path: TypePath::new(format!(
                    "{generic_path}<{}>",
                    registry.key_type(inner).meta.path
                ))
                .unwrap(),
                ..Default::default()
            },
            kind: crate::types::TypeKind::Array {
                ty: types::FieldType {
                    id: inner,
                    extra: Default::default(),
                },
                len: None,
            },
        }
    }

    fn from_bauble<Ctx: AssetContext>(
        val: Val,
        ctx: FromBaubleCtx<'_, 'a, DefaultAllocator, Ctx>,
    ) -> Result<Self, FromBaubleError> {
        let ty = ctx.get_type::<Self>(&val)?;
        if let Some((attribute, _)) = attributes.into_iter().next() {
            Err(FullDeserializeError::new::<Self>(
                span.clone(),
                DeserializeError::UnexpectedAttribute { attribute },
            ))?
        }

        Ok(match value {
            Value::Array(array) => array
                .into_iter()
                .map(|data| T::from_bauble(data, allocator))
                .collect::<Result<_, _>>()?,
            _ => Err(FullDeserializeError::new::<Self>(
                span,
                DeserializeError::WrongKind {
                    expected: ValueKind::Array,
                    found: value.kind(),
                },
            ))?,
        })
    }
}

impl<'a, A: BaubleAllocator<'a>> Bauble<'a, A> for bool {
    fn construct_type(_: &mut types::TypeRegistry) -> types::Type {
        types::Type {
            meta: types::TypeMeta {
                path: TypePath::new("bool").unwrap().to_owned(),
                ..Default::default()
            },
            kind: types::Primitive::Bool.into(),
        }
    }

    fn from_bauble(val: Val, allocator: &A) -> Result<A::Out<Self>, FromBaubleError> {
        match_val!(
            val,
            (Bool(v), _span) => {
                // SAFETY: No allocations are contained in a bool.
                unsafe { allocator.wrap(v) }
            }
        )
    }
}

impl Bauble<'_> for String {
    fn construct_type(_: &mut types::TypeRegistry) -> types::Type {
        types::Type {
            meta: types::TypeMeta {
                path: TypePath::new("std::string::String").unwrap().to_owned(),
                ..Default::default()
            },
            kind: types::Primitive::Str.into(),
        }
    }

    fn from_bauble(val: Val, _: &DefaultAllocator) -> Result<Self, FromBaubleError> {
        match_val!(
            val,
            (Str(string), _span) => string,
        )
    }
}

impl<'a, A: BaubleAllocator<'a>, T: Bauble<'a, A>> Bauble<'a, A> for Option<T> {
    fn construct_type(registry: &mut types::TypeRegistry) -> types::Type {
        let inner = registry.get_or_register_type::<T, _>();

        let generic_path = TypePath::new("std::option::Option").unwrap();
        let generic = registry.get_or_register_generic_type(generic_path);

        let kind = registry.build_enum([
            (
                TypePathElem::new("Some").unwrap(),
                types::Fields::Unnamed(types::TupleType {
                    required: vec![types::FieldType {
                        id: inner,
                        extra: IndexMap::new(),
                    }],
                    ..Default::default()
                }),
            ),
            (TypePathElem::new("None").unwrap(), types::Fields::Unit),
        ]);

        types::Type {
            meta: types::TypeMeta {
                generic_base_type: Some(generic),
                path: TypePath::new(format!(
                    "{generic_path}<{}>",
                    registry.key_type(inner).meta.path
                ))
                .unwrap(),
                ..Default::default()
            },
            kind,
        }
    }

    fn from_bauble(val: Val, allocator: &A) -> Result<A::Out<Option<T>>, FromBaubleError> {
        match_val!(
            val,
            (Struct(opt), _span) => {
                let opt = opt
                .map(|val| T::from_bauble(*val, allocator).and_then(|t| {
                    // SAFETY: We wrap this value again inside the option.
                    unsafe { allocator.validate(t) }
                }))
                .transpose();

                // SAFETY: The contained value in the option was validated,
                // and outside of that option doesn't contain any allocations.
                unsafe { opt.map(|opt| allocator.wrap(opt))? }
            }
        )
    }
}

macro_rules! impl_tuple {
    () => {};
    ($head:ident $($X:ident)*) => {
        impl_tuple!($($X)*);
        impl_tuple!(~ $head $($X)*);
    };
    (~ $($ident:ident)+) => {
        impl<'a, A: BaubleAllocator<'a>, $($ident: Bauble<'a, A>),*> Bauble<'a, A> for ($($ident),*,) {
            fn construct_type(registry: &mut types::TypeRegistry) -> types::Type {
                let mut inner_types = Vec::new();
                let mut path = "(".to_string();
                let mut _add_comma = false;
                $(
                    if _add_comma {
                        path.push_str(", ");
                    }
                    let inner = registry.get_or_register_type::<$ident, _>();
                    inner_types.push(types::FieldType {
                        id: inner,
                        extra: IndexMap::new(),
                    });
                    path.push_str(registry.key_type(inner).meta.path.as_str());
                    _add_comma = true;
                )*
                path.push_str(")");
                types::Type {
                    meta: types::TypeMeta {
                        path: TypePath::new(path).unwrap(),
                        ..Default::default()
                    },
                    kind: types::TypeKind::Tuple(types::TupleType {
                        required: inner_types,
                        optional: vec![],
                        allow_additional: None,
                    }),
                }
            }

            fn from_bauble(
                val: Val,
                allocator: &A,
            ) -> Result<A::Out<Self>, FromBaubleError> {
                const LEN: usize = [$(stringify!($ident)),*].len();
                match_val!(
                    val,
                    (Tuple(seq), span) => {
                        if seq.len() == LEN {
                            let mut seq = seq.into_iter();
                            let res = ($({
                                // SAFETY: We checked that the length of the sequence is the same as the
                                // length of this tuple type and this is only called once per element.
                                let elem = unsafe { seq.next().unwrap_unchecked() };
                                let elem = $ident::from_bauble(elem, allocator)?;

                                // SAFETY: We wrap the whole tuple containing this value.
                                unsafe { allocator.validate(elem)? }
                            }),*,);

                            // SAFETY: The contained vlaues have been validated.
                            unsafe { allocator.wrap(res) }


                        } else {
                            Err(DeserializeError::new::<Self>(span, DeserializeErrorKind::WrongTupleLength {
                                expected: LEN,
                                found: seq.len(),
                            }))?
                        }
                    }
                )
            }
        }
    };
}

impl_tuple!(T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15);

impl<'a, A: BaubleAllocator<'a>, T: Bauble<'a, A>, const N: usize> Bauble<'a, A> for [T; N] {
    fn construct_type(registry: &mut types::TypeRegistry) -> types::Type {
        let inner = registry.get_or_register_type::<T, _>();

        types::Type {
            meta: types::TypeMeta {
                path: TypePath::new(format!("[{}; {N}]", registry.key_type(inner).meta.path))
                    .unwrap(),
                ..Default::default()
            },
            kind: crate::types::TypeKind::Array {
                ty: types::FieldType {
                    id: inner,
                    extra: Default::default(),
                },
                len: Some(N),
            },
        }
    }

    fn from_bauble(val: Val, allocator: &A) -> Result<A::Out<Self>, FromBaubleError> {
        match_val!(
            val,
            (Array(seq), span) => {
                if seq.len() == N {
                    let res = <[T; N]>::try_from(
                        seq.into_iter()
                            .map(|s|
                                T::from_bauble(s, allocator).and_then(|elem| {
                                    // SAFETY: The elements are wrapped in the array.
                                    unsafe {
                                        allocator.validate(elem)
                                    }
                                })
                            )
                            .try_collect::<Vec<_>>()?,
                    )
                    .map_err(|_| ())
                    .expect("We checked the length");
                    // SAFETY: The elements have been validated.
                    unsafe { allocator.wrap(res) }
                } else {
                    Err(Box::new(FullDeserializeError::new::<Self>(span, DeserializeError::WrongArrayLength {
                        expected: N,
                        found: seq.len(),
                    })))?
                }
            }
        )
    }
}

#[cfg(feature = "enumset")]
impl<'a, A, T> Bauble<'a, A> for enumset::EnumSet<T>
where
    A: BaubleAllocator<'a>,
    T: Bauble<'a, A> + enumset::EnumSetType,
{
    fn construct_type(registry: &mut types::TypeRegistry) -> types::Type {
        let inner = registry.get_or_register_type::<T>();

        let generic_path = TypePath::new("enumset::EnumSet").unwrap();
        let generic = registry.get_or_register_generic_type(generic_path);

        types::Type {
            meta: types::TypeMeta {
                generic_base_type: Some(generic),
                path: TypePath::new(format!(
                    "{generic_path}<{}>",
                    registry.key_type(inner).meta.path
                ))
                .unwrap(),
                ..Default::default()
            },
            kind: crate::types::TypeKind::Array {
                ty: inner,
                len: None,
            },
        }
    }

    fn from_bauble(val: Val, allocator: &A) -> Result<A::Out<Self>, FromBaubleError> {
        match_val!(
            val,
            /*
            // TODO: Parse bitflags.
            (BitFlags(ty, flags), span) => {
                if let Some(ty) = ty {
                    let res = flags.into_iter().map(|flag| {
                        let enum_value = Val { value: Spanned { span: flag.span, value: Value::Enum(ty.clone(), flag, crate::FieldsKind::Unit) }, attributes: Spanned::empty() };

                        let value = T::from_bauble(enum_value, allocator)?;

                        // SAFETY: These are wrapped in the enumset. Which doesn't contain allocations.
                        unsafe { allocator.validate(value) }
                    }).try_collect()?;

                    // SAFETY: The elements were wrapped with the same allocator.
                    unsafe { allocator.wrap(res) }
                } else {
                    Err(DeserializeError::UnknownType { expected: <T as FromBauble<'a, A>>::INFO.to_owned(), span })?
                }
            }
            */
            (Array(array), _span) => {
                let res = array.into_iter().map(|value| {
                    let value = T::from_bauble(value, allocator)?;

                    // SAFETY: These are wrapped in the enumset. Which doesn't contain allocations.
                    unsafe { allocator.validate(value) }
                }).try_collect()?;

                // SAFETY: The elements were wrapped with the same allocator.
                unsafe { allocator.wrap(res) }
            }
        )
    }
}

macro_rules! impl_hash_map {
    ($($part:ident)::+) => {
        impl<'a, K: Bauble<'a> + Eq + std::hash::Hash, V: Bauble<'a>> Bauble<'a>
            for $($part)::+<K, V>
        {
            fn construct_type(registry: &mut types::TypeRegistry) -> types::Type {
                let key = registry.get_or_register_type::<K, _>();
                let value = registry.get_or_register_type::<V, _>();

                let generic_path = TypePath::new(stringify!($($part)::+)).unwrap();
                let generic = registry.get_or_register_generic_type(generic_path);

                types::Type {
                    meta: types::TypeMeta {
                        generic_base_type: Some(generic),
                        path: TypePath::new(format!(
                            "{generic_path}<{}, {}>",
                            registry.key_type(key).meta.path,
                            registry.key_type(value).meta.path
                        )).unwrap(),
                        ..Default::default()
                    },
                    kind: crate::types::TypeKind::Map {
                        key: types::FieldType {
                            id: key,
                            extra: Default::default(),
                        },
                        value: types::FieldType {
                            id: value,
                            extra: Default::default(),
                        },
                        len: None,
                    },
                }
            }

            fn from_bauble(
                val: Val,
                allocator: &DefaultAllocator,
            ) -> Result<<DefaultAllocator as BaubleAllocator>::Out<Self>, FromBaubleError> {
                match_val!(
                    val,
                    (Map(seq), _span) => {
                        seq
                            .into_iter()
                            .map(|(k, v)| {
                                Ok::<(K, V), FromBaubleError>((
                                    K::from_bauble(k, allocator)?,
                                    V::from_bauble(v, allocator)?,
                                ))
                            })
                            .try_collect()?
                    }
                )
            }
        }
    };
}

impl_hash_map!(std::collections::HashMap);

#[cfg(feature = "hashbrown")]
impl_hash_map!(hashbrown::HashMap);

impl<'a, T: Bauble<'a>> Bauble<'a> for Box<T> {
    fn construct_type(registry: &mut types::TypeRegistry) -> types::Type {
        let inner = registry.get_or_register_type::<T, _>();

        let generic_path = TypePath::new("std::box::Box").unwrap();
        let generic = registry.get_or_register_generic_type(generic_path);
        let ty = registry.key_type(inner);
        types::Type {
            meta: types::TypeMeta {
                generic_base_type: Some(generic),
                path: TypePath::new(format!("{generic_path}<{}>", ty.meta.path)).unwrap(),
                // TODO: Do we want to pass traits to box? Maybe have a field on the trait data whether to do that.
                traits: Vec::new(),
                attributes: ty.meta.attributes.clone(),
                extra: ty.meta.extra.clone(),
            },
            kind: types::TypeKind::Transparent(inner),
        }
    }

    fn from_bauble(
        val: Val,
        allocator: &DefaultAllocator,
    ) -> Result<<DefaultAllocator as BaubleAllocator>::Out<Self>, FromBaubleError> {
        Ok(Box::new(T::from_bauble(val, allocator)?))
    }
}
*/

impl Bauble<'_> for Val {
    fn construct_type(_: &mut types::TypeRegistry) -> types::Type {
        types::Type {
            meta: types::TypeMeta {
                attributes: types::NamedFields::any(),
                ..Default::default()
            },
            kind: types::TypeKind::Any,
        }
    }

    fn from_bauble<Ctx: AssetContext>(
        data: Val,
        _: FromBaubleCtx<'_, '_, DefaultAllocator, Ctx>,
    ) -> Result<Self, FromBaubleError> {
        Ok(data)
    }
}
*/
