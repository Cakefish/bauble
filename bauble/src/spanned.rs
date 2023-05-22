use std::{
    borrow::Borrow,
    fmt::{Debug, Display},
    hash::Hash,
    ops::{Deref, DerefMut},
};

use chumsky::span::SimpleSpan;

pub type Span = SimpleSpan;

#[derive(Clone)]
pub struct Spanned<T> {
    pub span: Span,
    pub value: T,
}

impl<T: PartialEq> PartialEq for Spanned<T> {
    fn eq(&self, other: &Self) -> bool {
        self.value.eq(&other.value)
    }
}

impl<T: Eq> Eq for Spanned<T> {}

impl<T: Hash> Hash for Spanned<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.value.hash(state);
    }
}

impl Borrow<str> for Spanned<&str> {
    fn borrow(&self) -> &str {
        self.value
    }
}

impl Borrow<str> for Spanned<String> {
    fn borrow(&self) -> &str {
        self.value.as_str()
    }
}

impl<T> Deref for Spanned<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

impl<T> DerefMut for Spanned<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.value
    }
}

impl<T> Spanned<T> {
    pub fn new(span: Span, value: T) -> Self {
        Self { span, value }
    }

    pub fn empty() -> Self
    where
        T: Default,
    {
        Self {
            span: (0..0).into(),
            value: T::default(),
        }
    }

    pub fn map<U>(self, mut map: impl FnMut(T) -> U) -> Spanned<U> {
        Spanned::new(self.span, map(self.value))
    }

    pub fn to_inner(self) -> T {
        self.value
    }
}
impl<T: Debug> Debug for Spanned<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "From: {}, To: {} ", self.span.start, self.span.end)?;
        self.value.fmt(f)
    }
}

impl<T: Display> Display for Spanned<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.value.fmt(f)
    }
}

pub trait SpanExt: Sized {
    fn span(self, span: Span) -> Spanned<Self>;

    fn empty(self) -> Spanned<Self> {
        Spanned::new((0..0).into(), self)
    }
}

impl<T: Sized> SpanExt for T {
    fn span(self, span: Span) -> Spanned<Self> {
        Spanned::new(span, self)
    }
}
