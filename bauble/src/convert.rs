use crate::{
    parse::{Ident, Path},
    spanned::{Span, Spanned},
    value::{ConvertionError, TypeInfo},
    Attributes, Val, Value, ValueKind,
};
use num_traits::ToPrimitive;
#[derive(Debug, PartialEq)]
pub enum VariantKind {
    Struct,
    Tuple,
    Path,
}

#[derive(Debug, PartialEq)]
pub enum DeserializeError {
    WrongTypePath {
        expected: TypeInfo,
        found: Spanned<TypeInfo>,
    },
    MissingTypePath {
        ty: TypeInfo,
        span: Span,
    },
    MissingField {
        field: String,
        ty: TypeInfo,
        span: Span,
    },
    UnexpectedField {
        field: Ident,
        ty: TypeInfo,
    },
    WrongTupleLength {
        expected: usize,
        found: usize,
        ty: TypeInfo,
        span: Span,
    },
    WrongArrayLength {
        expected: usize,
        found: usize,
        ty: TypeInfo,
        span: Span,
    },
    UnknownVariant {
        variant: Spanned<String>,
        kind: VariantKind,
        ty: TypeInfo,
    },
    WrongFields {
        found: VariantKind,
        expected: VariantKind,
        ty: TypeInfo,
    },
    MissingVariantName {
        ty: TypeInfo,
        span: Span,
    },
    NotAVariant {
        ty: TypeInfo,
        path: Spanned<Path>,
    },
    UnexpectedAttribute {
        attribute: Ident,
        ty: TypeInfo,
    },
    WrongKind {
        expected: ValueKind,
        found: ValueKind,
        ty: TypeInfo,
        span: Span,
    },
    WrongKindForId {
        expected: String,
        found: ValueKind,
        ty: String,
        span: Span,
    },
    Custom {
        message: String,
        span: Span,
    },
    Convertion(Spanned<ConvertionError>),
}

// TODO Maybe `unsafe trait`?
pub trait BaubleAllocator {
    type Out<T>;

    /// # Safety
    /// Allocations in `value` have to be allocated with the allocator from `allocator`
    unsafe fn wrap<T>(&self, value: T) -> Self::Out<T>;
    fn validate<T>(&self, value: Self::Out<T>) -> Result<T, Box<DeserializeError>>;
}

pub struct DefaultAllocator;

impl BaubleAllocator for DefaultAllocator {
    type Out<T> = T;

    unsafe fn wrap<T>(&self, value: T) -> Self::Out<T> {
        value
    }

    fn validate<T>(&self, value: Self::Out<T>) -> Result<T, Box<DeserializeError>> {
        Ok(value)
    }
}

pub trait FromBauble<A: BaubleAllocator = DefaultAllocator>: Sized {
    fn from_bauble(data: Val, allocator: &A) -> Result<A::Out<Self>, Box<DeserializeError>>;
}

impl<T: FromBauble> FromBauble for Vec<T> {
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
    ) -> Result<Self, Box<DeserializeError>> {
        if let Some((attribute, _)) = attributes.into_iter().next() {
            Err(DeserializeError::UnexpectedAttribute {
                attribute,
                ty: TypeInfo::simple("Vec"),
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
                ty: TypeInfo::simple("Vec"),
                span,
            })?,
        })
    }
}

macro_rules! impl_nums {
    ($($ty:ty,)*) => {
        $(
            impl<A: BaubleAllocator> FromBauble<A> for $ty {
                fn from_bauble(
                    Val {
                        attributes: Spanned { value: Attributes(attributes), .. },
                        value: Spanned { value, span },
                    }: Val,
                    allocator: &A,
                ) -> Result<A::Out<Self>, Box<DeserializeError>> {
                    if let Some((attribute, _)) = attributes.into_iter().next() {
                        Err(DeserializeError::UnexpectedAttribute {
                            attribute,
                            ty: TypeInfo::simple(stringify!($ty)),
                        })?
                    }

                    Ok(match value {
                        Value::Num(number) => {
                            let number = paste::paste!(number.[< to_ $ty >]())
                                .ok_or_else(|| DeserializeError::Custom {
                                    message: format!("{} is not a valid {}", number, stringify!($ty)),
                                    span,
                                })?;
                            // SAFETY: No allocations are contained in these types.
                            unsafe { allocator.wrap(number) }
                        },
                        _ => Err(DeserializeError::WrongKind {
                            expected: ValueKind::Num,
                            found: value.kind(),
                            ty: TypeInfo::simple(stringify!($ty)),
                            span,
                        })?,
                    })
                }
            }
        )*
    };
}

impl_nums! {
    u8, u16, u32, u64, u128,
    i8, i16, i32, i64, i128,
    f32, f64,
}

impl<A: BaubleAllocator> FromBauble<A> for bool {
    fn from_bauble(
        Val {
            attributes: Spanned { value: Attributes(attributes), .. },
            value: Spanned { value, span },
        }: Val,
        allocator: &A,
    ) -> Result<A::Out<Self>, Box<DeserializeError>> {
        if let Some((attribute, _)) = attributes.into_iter().next() {
            Err(DeserializeError::UnexpectedAttribute {
                attribute,
                ty: TypeInfo::simple("bool"),
            })?
        }

        Ok(match value {
            Value::Bool(v) => {
                // TODO: No allocations are contained in a bool.
                unsafe { allocator.wrap(v) }
            },
            _ => Err(DeserializeError::WrongKind {
                expected: ValueKind::Num,
                found: value.kind(),
                ty: TypeInfo::simple(stringify!($ty)),
                span,
            })?,
        })
    }
}

impl FromBauble for String {
    fn from_bauble(
        Val {
            attributes:
                Spanned {
                    value: Attributes(attributes),
                    ..
                },
            value: Spanned { value, span },
        }: Val,
        _: &DefaultAllocator,
    ) -> Result<Self, Box<DeserializeError>> {
        if let Some((attribute, _)) = attributes.into_iter().next() {
            Err(DeserializeError::UnexpectedAttribute {
                attribute,
                ty: TypeInfo::simple("String"),
            })?
        }

        Ok(match value {
            Value::Str(string) => string,
            _ => Err(DeserializeError::WrongKind {
                expected: ValueKind::Str,
                found: value.kind(),
                ty: TypeInfo::simple("String"),
                span,
            })?,
        })
    }
}

impl<A: BaubleAllocator, T: FromBauble<A>> FromBauble<A> for Option<T> {
    fn from_bauble(
        Val {
            attributes:
                Spanned {
                    value: Attributes(attributes),
                    ..
                },
            value: Spanned { value, span },
        }: Val,
        allocator: &A,
    ) -> Result<A::Out<Option<T>>, Box<DeserializeError>> {
        if let Some((attribute, _)) = attributes.into_iter().next() {
            Err(DeserializeError::UnexpectedAttribute {
                attribute,
                ty: TypeInfo::simple("Option"),
            })?
        }

        match value {
            Value::Opt(opt) => {
                let opt = opt
                .map(|val| T::from_bauble(*val, allocator).and_then(|t| allocator.validate(t)))
                .transpose();

                // SAFETY: The contained value in the option was validated,
                // and outside of that option doesn't contain any allocations.
                unsafe { opt.map(|opt| allocator.wrap(opt)) }
            },
            _ => Err(Box::new(DeserializeError::WrongKind {
                expected: ValueKind::Unit,
                found: value.kind(),
                ty: TypeInfo::simple("Option"),
                span,
            })),
        }
    }
}

impl FromBauble for () {
    fn from_bauble(
        Val {
            attributes:
                Spanned {
                    value: Attributes(attributes),
                    ..
                },
            value: Spanned { value, span },
        }: Val,
        _: &DefaultAllocator,
    ) -> Result<Self, Box<DeserializeError>> {
        if let Some((attribute, _)) = attributes.into_iter().next() {
            Err(DeserializeError::UnexpectedAttribute {
                attribute,
                ty: TypeInfo::simple("()"),
            })?
        }

        match value {
            Value::Unit => (),
            _ => Err(DeserializeError::WrongKind {
                expected: ValueKind::Unit,
                found: value.kind(),
                ty: TypeInfo::simple("()"),
                span,
            })?,
        }

        Ok(())
    }
}

macro_rules! impl_tuple {
    ($($ident:ident),+) => {
        impl<$($ident: FromBauble),*> FromBauble for ($($ident),*,) {
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
            ) -> Result<Self, Box<DeserializeError>> {
                const LEN: usize = [$(stringify!($ident)),*].len();
                if let Some((attribute, _)) = attributes.into_iter().next() {
                    Err(DeserializeError::UnexpectedAttribute {
                        attribute,
                        ty: TypeInfo::simple("Tuple"),
                    })?
                }

                match value {
                    Value::Tuple(seq) => {
                        if seq.len() == LEN {
                            let mut seq = seq.into_iter();
                            Ok(($($ident::from_bauble(seq.next().expect("We checked tuple length"), allocator)?),*,))
                        } else {
                            Err(Box::new(DeserializeError::WrongTupleLength {
                                expected: LEN,
                                found: seq.len(),
                                ty: TypeInfo::simple("Tuple"),
                                span,
                            }))
                        }
                    },
                    _ => Err(Box::new(DeserializeError::WrongKind {
                        expected: ValueKind::Unit,
                        found: value.kind(),
                        ty: TypeInfo::simple("Tuple"),
                        span,
                    })),
                }
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

impl<T: FromBauble, const N: usize> FromBauble for [T; N] {
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
    ) -> Result<<DefaultAllocator as BaubleAllocator>::Out<Self>, Box<DeserializeError>> {
        if let Some((attribute, _)) = attributes.into_iter().next() {
            Err(DeserializeError::UnexpectedAttribute {
                attribute,
                ty: TypeInfo::simple("Array"),
            })?
        }

        match value {
            Value::Array(seq) => {
                if seq.len() == N {
                    let seq = <[T; N]>::try_from(
                        seq.into_iter()
                            .map(|s| T::from_bauble(s, allocator).map(|i| i))
                            .try_collect::<Vec<_>>()?,
                    )
                    .map_err(|_| ())
                    .expect("We checked the length");
                    Ok(seq)
                } else {
                    Err(Box::new(DeserializeError::WrongArrayLength {
                        expected: N,
                        found: seq.len(),
                        ty: TypeInfo::simple("Tuple"),
                        span,
                    }))
                }
            }
            _ => Err(Box::new(DeserializeError::WrongKind {
                expected: ValueKind::Unit,
                found: value.kind(),
                ty: TypeInfo::simple("Tuple"),
                span,
            })),
        }
    }
}

impl<K: FromBauble + Eq + std::hash::Hash, V: FromBauble> FromBauble
    for std::collections::HashMap<K, V>
{
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
    ) -> Result<<DefaultAllocator as BaubleAllocator>::Out<Self>, Box<DeserializeError>> {
        if let Some((attribute, _)) = attributes.into_iter().next() {
            Err(DeserializeError::UnexpectedAttribute {
                attribute,
                ty: TypeInfo::simple("std::collections::HashMap"),
            })?
        }

        match value {
            Value::Map(seq) => {
                let seq = seq
                    .into_iter()
                    .map(|(k, v)| {
                        Ok::<(K, V), Box<DeserializeError>>((
                            K::from_bauble(k, allocator)?,
                            V::from_bauble(v, allocator)?,
                        ))
                    })
                    .try_collect()?;
                Ok(seq)
            }
            _ => Err(Box::new(DeserializeError::WrongKind {
                expected: ValueKind::Unit,
                found: value.kind(),
                ty: TypeInfo::simple("Tuple"),
                span,
            })),
        }
    }
}
