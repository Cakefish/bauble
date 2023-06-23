use std::{error::Error, fmt::Display};

use crate::{
    parse::{Ident, Path},
    spanned::{Span, SpanExt, Spanned},
    value::{ConversionError, OwnedTypeInfo},
    Attributes, TypeInfo, Val, Value, ValueKind,
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
        found: Spanned<OwnedTypeInfo>,
    },
    MissingTypePath {
        ty: Option<OwnedTypeInfo>,
        span: Span,
    },
    UnexpectedTypePath {
        ty: Spanned<OwnedTypeInfo>,
    },
    MissingField {
        field: String,
        ty: OwnedTypeInfo,
        span: Span,
    },
    UnexpectedField {
        field: Ident,
        ty: OwnedTypeInfo,
    },
    WrongTupleLength {
        expected: usize,
        found: usize,
        ty: OwnedTypeInfo,
        span: Span,
    },
    WrongArrayLength {
        expected: usize,
        found: usize,
        ty: OwnedTypeInfo,
        span: Span,
    },
    UnknownVariant {
        variant: Spanned<String>,
        kind: VariantKind,
        ty: OwnedTypeInfo,
    },
    UnknownFlattenedVariant {
        variant: Spanned<OwnedTypeInfo>,
        ty: OwnedTypeInfo,
    },
    WrongFields {
        found: VariantKind,
        expected: VariantKind,
        ty: OwnedTypeInfo,
        span: Span,
    },
    MissingVariantName {
        ty: OwnedTypeInfo,
        span: Span,
    },
    NotAVariant {
        ty: OwnedTypeInfo,
        path: Spanned<Path>,
    },
    UnexpectedAttribute {
        attribute: Ident,
        ty: OwnedTypeInfo,
    },
    WrongKind {
        expected: ValueKind,
        found: ValueKind,
        ty: OwnedTypeInfo,
        span: Span,
    },
    Custom {
        message: String,
        span: Span,
    },
    Convertion(Spanned<ConversionError>),
}

impl Display for DeserializeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use DeserializeError::*;

        match self {
            WrongTypePath {
                expected,
                found: Spanned { span, value },
            } => write!(f, "{span}: expected path `{expected}`, found `{value}`"),
            MissingTypePath { ty: Some(ty), span } => write!(f, "{span}: missing type path `{ty}`"),
            MissingTypePath { ty: None, span } => write!(f, "{span}: missing type path"),
            UnexpectedTypePath {
                ty: Spanned { span, value },
            } => write!(f, "{span}: unexpected type path `{value}`"),
            MissingField { field, ty, span } => {
                write!(f, "{span}: missing field `{field}` in `{ty}`")
            }
            UnexpectedField {
                field: Spanned { span, value },
                ty,
            } => write!(f, "{span}: unexpected field `{value}` in `{ty}`"),
            WrongTupleLength {
                expected,
                found,
                ty,
                span,
            } => write!(
                f,
                "{span}: wrong tuple length, expected `{expected}`, found `{found}` in `{ty}`"
            ),
            WrongArrayLength {
                expected,
                found,
                ty,
                span,
            } => write!(
                f,
                "{span}: wrong array length, expected `{expected}`, found `{found}` in `{ty}`"
            ),
            UnknownVariant {
                variant: Spanned { span, value },
                kind,
                ty,
            } => write!(
                f,
                "{span}: unknown variant `{value}` of kind {kind} in `{ty}`"
            ),
            UnknownFlattenedVariant {
                variant: Spanned { span, value },
                ty,
            } => write!(f, "{span}: unknown flattened variant `{value}` in `{ty}`"),
            WrongFields {
                found,
                expected,
                ty,
                span,
            } => write!(
                f,
                "{span}: wrong fields, expected {expected}, found {found} in `{ty}`"
            ),
            MissingVariantName { ty, span } => {
                write!(f, "{span}: missing variant name in `{ty}`")
            }
            NotAVariant {
                ty,
                path: Spanned { span, value },
            } => write!(f, "{span}: `{value}` is not a variant of `{ty}`"),
            UnexpectedAttribute {
                attribute: Spanned { span, value },
                ty,
            } => write!(f, "{span}: unexpected attribute `{value}` in `{ty}`"),
            WrongKind {
                expected,
                found,
                ty,
                span,
            } => write!(
                f,
                "{span}: wrong kind, expected {expected}, found {found} in `{ty}`"
            ),
            Custom { message, span } => write!(f, "{span}: {message}"),
            Convertion(Spanned { span, value }) => write!(f, "{span}: {value}"),
        }
    }
}

impl Error for DeserializeError {}

impl DeserializeError {
    pub fn err_span(&self) -> Span {
        use DeserializeError::*;

        let (&WrongTypePath {
            found: Spanned { span, .. },
            ..
        }
        | &MissingTypePath { span, .. }
        | &UnexpectedTypePath {
            ty: Spanned { span, .. },
        }
        | &MissingField { span, .. }
        | &UnexpectedField {
            field: Spanned { span, .. },
            ..
        }
        | &WrongTupleLength { span, .. }
        | &WrongArrayLength { span, .. }
        | &UnknownVariant {
            variant: Spanned { span, .. },
            ..
        }
        | &UnknownFlattenedVariant {
            variant: Spanned { span, .. },
            ..
        }
        | &WrongFields { span, .. }
        | &MissingVariantName { span, .. }
        | &NotAVariant {
            path: Spanned { span, .. },
            ..
        }
        | &UnexpectedAttribute {
            attribute: Spanned { span, .. },
            ..
        }
        | &WrongKind { span, .. }
        | &Custom { span, .. }
        | &Convertion(Spanned { span, .. })) = self;
        span
    }
}

// TODO Maybe `unsafe trait`?
pub trait BaubleAllocator<'a> {
    type Out<T>
    where
        Self: 'a;

    /// # Safety
    /// Allocations in `value` have to be allocated with the allocator from `allocator`
    unsafe fn wrap<T>(&'a self, value: T) -> Self::Out<T>;
    /// # Safety
    /// If validated an item must be placed within the same allocator.
    unsafe fn validate<T>(&'a self, value: Self::Out<T>) -> Result<T, Box<DeserializeError>>;
}

pub struct DefaultAllocator;

impl<'a> BaubleAllocator<'a> for DefaultAllocator {
    type Out<T> = T;

    unsafe fn wrap<T>(&'a self, value: T) -> Self::Out<T> {
        value
    }

    unsafe fn validate<T>(&'a self, value: Self::Out<T>) -> Result<T, Box<DeserializeError>> {
        Ok(value)
    }
}

pub trait FromBauble<'a, A: BaubleAllocator<'a> = DefaultAllocator>: Sized {
    const INFO: TypeInfo<'static>;

    fn from_bauble(data: Val, allocator: &'a A) -> Result<A::Out<Self>, Box<DeserializeError>>;
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
        allocator: &'a DefaultAllocator,
    ) -> Result<Self, Box<DeserializeError>> {
        if let Some((attribute, _)) = attributes.into_iter().next() {
            Err(DeserializeError::UnexpectedAttribute {
                attribute,
                ty: Self::INFO.to_owned(),
            })?
        }

        Ok(match value {
            Value::Array(array) => array
                .into_iter()
                .map(|data| T::from_bauble(data, allocator).map(|value| value))
                .collect::<Result<_, _>>()?,
            _ => Err(DeserializeError::WrongKind {
                expected: ValueKind::Array,
                found: value.kind(),
                ty: Self::INFO.to_owned(),
                span,
            })?,
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
                Err($crate::DeserializeError::UnexpectedAttribute {
                    attribute: attribute.clone(),
                    ty: $crate::OwnedTypeInfo::Kind($crate::ValueKind::$ident),
                })?
            }

            let $crate::Spanned { value, span } = value.value;
            Ok(match (value, span) {
                ($crate::Value::$ident $(($($field),+))?, $span) => $block,
                (value, span) => Err($crate::DeserializeError::WrongKind {
                    expected: $crate::ValueKind::$ident,
                    found: value.kind(),
                    ty: $crate::OwnedTypeInfo::Kind($crate::ValueKind::$ident),
                    span,
                })?,
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
                    allocator: &'a A,
                ) -> Result<A::Out<Self>, Box<DeserializeError>> {
                    match_val!(
                        val,
                        (Num(number), span) => {
                            let number = paste::paste!(number.[< to_ $ty >]())
                                .ok_or_else(|| DeserializeError::Custom {
                                    message: format!("{} is not a valid {}", number, stringify!($ty)),
                                    span,
                                })?;
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

    fn from_bauble(val: Val, allocator: &'a A) -> Result<A::Out<Self>, Box<DeserializeError>> {
        match_val!(
            val,
            (Bool(v), _span) => {
                // SAFETY: No allocations are contained in a bool.
                unsafe { allocator.wrap(v) }
            }
        )
    }
}

impl<'a> FromBauble<'a> for String {
    const INFO: TypeInfo<'static> = TypeInfo::Kind(ValueKind::Str);

    fn from_bauble(val: Val, _: &DefaultAllocator) -> Result<Self, Box<DeserializeError>> {
        match_val!(
            val,
            (Str(string), _span) => string,
        )
    }
}

impl<'a, A: BaubleAllocator<'a>, T: FromBauble<'a, A>> FromBauble<'a, A> for Option<T> {
    const INFO: TypeInfo<'static> = TypeInfo::Kind(ValueKind::Opt);

    fn from_bauble(val: Val, allocator: &'a A) -> Result<A::Out<Option<T>>, Box<DeserializeError>> {
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

impl<'a> FromBauble<'a> for () {
    const INFO: TypeInfo<'static> = TypeInfo::Kind(ValueKind::Unit);

    fn from_bauble(val: Val, _: &DefaultAllocator) -> Result<Self, Box<DeserializeError>> {
        match_val!(
            val,
            (Unit, _span) => (),
        )
    }
}

macro_rules! impl_tuple {
    ($($ident:ident),+) => {
        impl<'a, $($ident: FromBauble<'a>),*> FromBauble<'a> for ($($ident),*,) {
            const INFO: TypeInfo<'static> = TypeInfo::Kind(ValueKind::Tuple);

            fn from_bauble(
                val: Val,
                allocator: &'a DefaultAllocator,
            ) -> Result<Self, Box<DeserializeError>> {
                const LEN: usize = [$(stringify!($ident)),*].len();
                match_val!(
                    val,
                    (Tuple(name, seq), span) => {
                        if let Some(name) = name {
                            Err(DeserializeError::UnexpectedTypePath {
                                ty: name.span(span),
                            })?
                        }

                        if seq.len() == LEN {
                            let mut seq = seq.into_iter();
                            ($($ident::from_bauble(seq.next().expect("We checked tuple length"), allocator)?),*,)
                        } else {
                            Err(Box::new(DeserializeError::WrongTupleLength {
                                expected: LEN,
                                found: seq.len(),
                                ty: Self::INFO.to_owned(),
                                span,
                            }))?
                        }
                    }
                )
            }
        }
    };
}

impl_tuple!(T0);
impl_tuple!(T0, T1);
impl_tuple!(T0, T1, T2);
impl_tuple!(T0, T1, T2, T3);
impl_tuple!(T0, T1, T2, T3, T4);
impl_tuple!(T0, T1, T2, T3, T4, T5);
impl_tuple!(T0, T1, T2, T3, T4, T5, T6);
impl_tuple!(T0, T1, T2, T3, T4, T5, T6, T7);
impl_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8);
impl_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9);
impl_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10);
impl_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11);
impl_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12);
impl_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13);
impl_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14);
impl_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15);

impl<'a, T: FromBauble<'a>, const N: usize> FromBauble<'a> for [T; N] {
    const INFO: TypeInfo<'static> = TypeInfo::Kind(ValueKind::Array);

    fn from_bauble(
        val: Val,
        allocator: &'a DefaultAllocator,
    ) -> Result<<DefaultAllocator as BaubleAllocator>::Out<Self>, Box<DeserializeError>> {
        match_val!(
            val,
            (Array(seq), span) => {
                if seq.len() == N {
                    <[T; N]>::try_from(
                        seq.into_iter()
                            .map(|s| T::from_bauble(s, allocator).map(|i| i))
                            .try_collect::<Vec<_>>()?,
                    )
                    .map_err(|_| ())
                    .expect("We checked the length")
                } else {
                    Err(Box::new(DeserializeError::WrongArrayLength {
                        expected: N,
                        found: seq.len(),
                        ty: Self::INFO.to_owned(),
                        span,
                    }))?
                }
            }
        )
    }
}

impl<'a, K: FromBauble<'a> + Eq + std::hash::Hash, V: FromBauble<'a>> FromBauble<'a>
    for std::collections::HashMap<K, V>
{
    const INFO: TypeInfo<'static> = TypeInfo::Kind(ValueKind::Map);

    fn from_bauble(
        val: Val,
        allocator: &'a DefaultAllocator,
    ) -> Result<<DefaultAllocator as BaubleAllocator>::Out<Self>, Box<DeserializeError>> {
        match_val!(
            val,
            (Map(seq), _span) => {
                let seq = seq
                    .into_iter()
                    .map(|(k, v)| {
                        Ok::<(K, V), Box<DeserializeError>>((
                            K::from_bauble(k, allocator)?,
                            V::from_bauble(v, allocator)?,
                        ))
                    })
                    .try_collect()?;
                seq
            }
        )
    }
}

impl<'a, T: FromBauble<'a>> FromBauble<'a> for Box<T> {
    const INFO: TypeInfo<'static> = T::INFO;

    fn from_bauble(
        val: Val,
        allocator: &'a DefaultAllocator,
    ) -> Result<<DefaultAllocator as BaubleAllocator>::Out<Self>, Box<DeserializeError>> {
        Ok(Box::new(T::from_bauble(val, allocator)?))
    }
}
