use std::{
    borrow::Borrow,
    error::Error,
    fmt::{Debug, Display},
    hash::Hash,
    ops::{Deref, DerefMut, Range},
    sync::Arc,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
    path: Arc<str>,
}

impl std::fmt::Display for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<{}>:{}..{}", self.path, self.start, self.end)
    }
}

impl From<Span> for Arc<str> {
    fn from(value: Span) -> Self {
        value.path
    }
}

impl Span {
    pub fn new(file: impl Into<Arc<str>>, range: Range<usize>) -> Self {
        Self {
            start: range.start,
            end: range.end,
            path: file.into(),
        }
    }

    pub fn empty() -> Self {
        Self {
            start: 0,
            end: 0,
            path: "".into(),
        }
    }

    pub fn len(&self) -> usize {
        self.end - self.start
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.start == self.end
    }

    pub fn sub_span(&self, range: Range<usize>) -> Span {
        Span {
            path: self.path.clone(),
            start: self.start + range.start,
            end: self.end + range.end,
        }
    }
}

impl chumsky::span::Span for crate::Span {
    type Context = Arc<str>;
    type Offset = usize;

    fn new(context: Self::Context, range: Range<Self::Offset>) -> Self {
        Self {
            start: range.start,
            end: range.end,
            path: context,
        }
    }
    fn context(&self) -> Self::Context {
        self.path.clone()
    }
    fn start(&self) -> Self::Offset {
        self.start
    }
    fn end(&self) -> Self::Offset {
        self.end
    }
}

impl ariadne::Span for Span {
    type SourceId = Arc<str>;

    fn source(&self) -> &Self::SourceId {
        &self.path
    }

    fn start(&self) -> usize {
        self.start
    }

    fn end(&self) -> usize {
        self.end
    }
}

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
            span: Span::empty(),
            value: T::default(),
        }
    }

    pub fn map<U>(self, mut map: impl FnMut(T) -> U) -> Spanned<U> {
        Spanned::new(self.span, map(self.value))
    }

    pub fn to_inner(self) -> T {
        self.value
    }

    pub fn span(&self) -> Span {
        self.span.clone()
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

impl<T: Error> Error for Spanned<T> {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        self.value.source()
    }
}

pub trait SpanExt: Sized {
    fn spanned(self, span: Span) -> Spanned<Self>;

    fn empty(self) -> Spanned<Self> {
        Spanned::new(Span::empty(), self)
    }
}

impl<T: Sized> SpanExt for T {
    fn spanned(self, span: Span) -> Spanned<Self> {
        Spanned::new(span, self)
    }
}
