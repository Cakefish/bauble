use std::{borrow::Cow, fmt::Display};

use crate::{
    Attributes, TypeInfo, Val, Value, ValueKind,
    error::{BaubleError, ErrorMsg, Level},
    parse::Ident,
    spanned::{Span, SpanExt, Spanned},
    value::OwnedTypeInfo,
};
use num_traits::ToPrimitive;

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

#[derive(Debug, Clone, PartialEq)]
pub enum DeserializeError {
    WrongTypePath {
        expected: OwnedTypeInfo,
        path_span: Span,
    },
    UnexpectedTypePath {
        path_span: Span,
        ty: OwnedTypeInfo,
    },
    MissingField {
        field: String,
        ty: OwnedTypeInfo,
    },
    UnexpectedField {
        field: Ident,
        ty: OwnedTypeInfo,
    },
    WrongTupleLength {
        expected: usize,
        found: usize,
        ty: OwnedTypeInfo,
    },
    WrongArrayLength {
        expected: usize,
        found: usize,
        ty: OwnedTypeInfo,
    },
    UnknownVariant {
        variant: Ident,
        kind: VariantKind,
        ty: OwnedTypeInfo,
    },
    UnknownFlattenedVariant {
        variant: Spanned<OwnedTypeInfo>,
        ty: OwnedTypeInfo,
    },
    UnexpectedAttribute {
        attribute: Ident,
        ty: OwnedTypeInfo,
    },
    WrongKind {
        expected: ValueKind,
        found: ValueKind,
        ty: OwnedTypeInfo,
    },
    MissingAttribute {
        attribute: String,
        attributes_span: Span,
        ty: OwnedTypeInfo,
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

    pub fn error(self, span: Span) -> Spanned<DeserializeError> {
        DeserializeError::Custom(self).spanned(span)
    }
}

impl BaubleError for Spanned<DeserializeError> {
    fn level(&self) -> Level {
        match &self.value {
            DeserializeError::Custom(custom_error) => custom_error.level,
            _ => Level::Error,
        }
    }
    fn msg_general(&self) -> ErrorMsg {
        let msg = match &self.value {
            DeserializeError::WrongTypePath { .. } => Cow::Borrowed("Wrong type path"),
            DeserializeError::UnexpectedTypePath { ty, .. } => {
                Cow::Owned(format!("Unexpected type path for the type {ty}"))
            }
            DeserializeError::MissingField { ty, .. } => {
                Cow::Owned(format!("Missing field for the type {ty}"))
            }
            DeserializeError::UnexpectedField { ty, .. } => {
                Cow::Owned(format!("Unexpected field for the type {ty}"))
            }
            DeserializeError::WrongTupleLength { ty, .. } => {
                Cow::Owned(format!("Wrong tuple length for the type {ty}"))
            }
            DeserializeError::WrongArrayLength { ty, .. } => {
                Cow::Owned(format!("Wrong array length for the type {ty}"))
            }
            DeserializeError::UnknownVariant { ty, .. } => {
                Cow::Owned(format!("Unknown variant for the type {ty}"))
            }
            DeserializeError::UnknownFlattenedVariant { ty, .. } => {
                Cow::Owned(format!("Unknown flattened variant for the type {ty}"))
            }
            DeserializeError::UnexpectedAttribute { ty, .. } => {
                Cow::Owned(format!("Unexpected attribute for the type {ty}"))
            }
            DeserializeError::WrongKind { ty, .. } => {
                Cow::Owned(format!("Wrong kind for the type {ty}"))
            }
            DeserializeError::MissingAttribute { ty, .. } => {
                Cow::Owned(format!("Missing attributy for the type {ty}"))
            }
            DeserializeError::Custom(custom) => custom.message.clone(),
        };

        Spanned::new(self.span.clone(), msg)
    }

    fn msgs_specific(&self) -> Vec<(ErrorMsg, Level)> {
        match &self.value {
            DeserializeError::WrongTypePath {
                expected,
                path_span,
                ..
            } => {
                vec![(
                    Spanned::new(
                        path_span.clone(),
                        Cow::Owned(format!("Expected the path `{expected}`")),
                    ),
                    Level::Error,
                )]
            }
            DeserializeError::UnexpectedTypePath { path_span, .. } => {
                vec![(
                    Spanned::new(
                        path_span.clone(),
                        Cow::Borrowed("Didn't expect a path here"),
                    ),
                    Level::Error,
                )]
            }
            DeserializeError::MissingField { field, .. } => {
                vec![(
                    Spanned::new(
                        self.span(),
                        Cow::Owned(format!("Missing field the field {field}")),
                    ),
                    Level::Error,
                )]
            }
            DeserializeError::UnexpectedField { field, .. } => {
                vec![(
                    Spanned::new(field.span.clone(), Cow::Borrowed("Unexpected field")),
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
                        self.span(),
                        Cow::Owned(format!(
                            "Expected the length {expected}, found length {found}."
                        )),
                    ),
                    Level::Error,
                )]
            }
            DeserializeError::UnknownVariant { variant, .. } => {
                vec![(
                    Spanned::new(variant.span(), Cow::Borrowed("Unknown variant")),
                    Level::Error,
                )]
            }
            DeserializeError::UnknownFlattenedVariant { variant, .. } => {
                vec![(
                    Spanned::new(variant.span(), Cow::Borrowed("Unknown flattened variant")),
                    Level::Error,
                )]
            }
            DeserializeError::UnexpectedAttribute { attribute, .. } => {
                vec![(
                    Spanned::new(attribute.span(), Cow::Borrowed("Unexpected attribute")),
                    Level::Error,
                )]
            }
            DeserializeError::WrongKind {
                expected, found, ..
            } => {
                vec![(
                    Spanned::new(
                        self.span(),
                        Cow::Owned(format!("Expected the kind {expected}, found {found}")),
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
                        attributes_span.clone(),
                        Cow::Owned(format!("Missing the attribute `{attribute}`")),
                    ),
                    Level::Error,
                )]
            }
            DeserializeError::Custom(custom_error) => custom_error.labels.clone(),
        }
    }
}

pub type FromBaubleError = Box<Spanned<DeserializeError>>;

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

pub trait FromBauble<'a, A: BaubleAllocator<'a> = DefaultAllocator>: Sized {
    const INFO: TypeInfo<'static>;

    fn from_bauble(data: Val, allocator: &A) -> Result<A::Out<Self>, FromBaubleError>;
}

impl<'a, T: FromBauble<'a>> FromBauble<'a> for Vec<T> {
    const INFO: TypeInfo<'static> = TypeInfo::Kind(ValueKind::Array);

    fn from_bauble(
        Val {
            attributes:
                Spanned {
                    value: Attributes(attributes),
                    ..
                },
            value: Spanned { value, span },
        }: Val,
        allocator: &DefaultAllocator,
    ) -> Result<Self, FromBaubleError> {
        if let Some((attribute, _)) = attributes.into_iter().next() {
            let span = attribute.span();
            Err(DeserializeError::UnexpectedAttribute {
                attribute,
                ty: Self::INFO.to_owned(),
            }
            .spanned(span))?
        }

        Ok(match value {
            Value::Array(array) => array
                .into_iter()
                .map(|data| T::from_bauble(data, allocator))
                .collect::<Result<_, _>>()?,
            _ => Err(DeserializeError::WrongKind {
                expected: ValueKind::Array,
                found: value.kind(),
                ty: Self::INFO.to_owned(),
            }
            .spanned(span))?,
        })
    }
}

/// Match on a simple value, assumes no attributes, and only one valid Value to convert from.
#[macro_export]
macro_rules! match_val {
    ($value:expr, ($ident:ident$(($($field:ident),+))?, $span:ident) => $block:expr $(,)?) => {
        {
            let value = $value;
            if let Some((attribute, _)) = value.attributes.value.0.iter().next() {
                Err($crate::Spanned::new(attribute.span(), $crate::DeserializeError::UnexpectedAttribute {
                    attribute: attribute.clone(),
                    ty: $crate::OwnedTypeInfo::Kind($crate::ValueKind::$ident),
                }))?
            }

            let $crate::Spanned { value, span } = value.value;
            Ok(match (value, span) {
                ($crate::Value::$ident $(($($field),+))?, $span) => $block,
                (value, span) => Err($crate::Spanned::new(span, $crate::DeserializeError::WrongKind {
                    expected: $crate::ValueKind::$ident,
                    found: value.kind(),
                    ty: $crate::OwnedTypeInfo::Kind($crate::ValueKind::$ident),
                }))?,
            })
        }
    };
}

macro_rules! impl_nums {
    ($($ty:ty,)*) => {
        $(
            impl<'a, A: BaubleAllocator<'a>> FromBauble<'a, A> for $ty {
                const INFO: TypeInfo<'static> = TypeInfo::Kind(ValueKind::Num);

                fn from_bauble(
                    val: Val,
                    allocator: &A,
                ) -> Result<A::Out<Self>, FromBaubleError> {
                    match_val!(
                        val,
                        (Num(number), span) => {
                            let number = paste::paste!(number.[< to_ $ty >]())
                                .ok_or_else(|| DeserializeError::Custom(CustomError {
                                    message: Cow::Borrowed("Invalid number"),
                                    level: Level::Error,
                                    labels: vec![(Spanned::new(span.clone(), Cow::Owned(format!("{} is not a valid {}", number, stringify!($ty)))), Level::Error)]
                                }).spanned(span))?;
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

impl<'a, A: BaubleAllocator<'a>> FromBauble<'a, A> for bool {
    const INFO: TypeInfo<'static> = TypeInfo::Kind(ValueKind::Bool);

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

impl FromBauble<'_> for String {
    const INFO: TypeInfo<'static> = TypeInfo::Kind(ValueKind::Str);

    fn from_bauble(val: Val, _: &DefaultAllocator) -> Result<Self, FromBaubleError> {
        match_val!(
            val,
            (Str(string), _span) => string,
        )
    }
}

impl<'a, A: BaubleAllocator<'a>, T: FromBauble<'a, A>> FromBauble<'a, A> for Option<T> {
    const INFO: TypeInfo<'static> = TypeInfo::Kind(ValueKind::Opt);

    fn from_bauble(val: Val, allocator: &A) -> Result<A::Out<Option<T>>, FromBaubleError> {
        match_val!(
            val,
            (Opt(opt), _span) => {
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

impl FromBauble<'_> for () {
    const INFO: TypeInfo<'static> = TypeInfo::Kind(ValueKind::Unit);

    fn from_bauble(val: Val, _: &DefaultAllocator) -> Result<Self, FromBaubleError> {
        match_val!(
            val,
            (Unit, _span) => (),
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
        impl<'a, A: BaubleAllocator<'a>, $($ident: FromBauble<'a, A>),*> FromBauble<'a, A> for ($($ident),*,) {
            const INFO: TypeInfo<'static> = TypeInfo::Kind(ValueKind::Tuple);

            fn from_bauble(
                val: Val,
                allocator: &A,
            ) -> Result<A::Out<Self>, FromBaubleError> {
                const LEN: usize = [$(stringify!($ident)),*].len();
                match_val!(
                    val,
                    (Tuple(name, seq), span) => {
                        if let Some(name) = name {
                            Err(DeserializeError::UnexpectedTypePath {
                                ty: Self::INFO.to_owned(),
                                path_span: name.span(),
                            }.spanned(span.clone()))?
                        }

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
                            return Err(Box::new(DeserializeError::WrongTupleLength {
                                expected: LEN,
                                found: seq.len(),
                                ty: Self::INFO.to_owned(),
                            }.spanned(span)));
                        }
                    }
                )
            }
        }
    };
}

impl_tuple!(T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15);

impl<'a, A: BaubleAllocator<'a>, T: FromBauble<'a, A>, const N: usize> FromBauble<'a, A>
    for [T; N]
{
    const INFO: TypeInfo<'static> = TypeInfo::Kind(ValueKind::Array);

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
                    return Err(Box::new(DeserializeError::WrongArrayLength {
                        expected: N,
                        found: seq.len(),
                        ty: Self::INFO.to_owned(),
                    }.spanned(span)))
                }
            }
        )
    }
}

#[cfg(feature = "enumset")]
impl<'a, A, T> FromBauble<'a, A> for enumset::EnumSet<T>
where
    A: BaubleAllocator<'a>,
    T: FromBauble<'a, A> + enumset::EnumSetType,
{
    const INFO: TypeInfo<'static> = TypeInfo::Kind(ValueKind::Array);

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
        impl<'a, K: FromBauble<'a> + Eq + std::hash::Hash, V: FromBauble<'a>> FromBauble<'a>
            for $($part)::+<K, V>
        {
            const INFO: TypeInfo<'static> = TypeInfo::Kind(ValueKind::Map);

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

impl<'a, T: FromBauble<'a>> FromBauble<'a> for Box<T> {
    const INFO: TypeInfo<'static> = T::INFO;

    fn from_bauble(
        val: Val,
        allocator: &DefaultAllocator,
    ) -> Result<<DefaultAllocator as BaubleAllocator>::Out<Self>, FromBaubleError> {
        Ok(Box::new(T::from_bauble(val, allocator)?))
    }
}
