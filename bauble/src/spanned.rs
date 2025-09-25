use std::{
    borrow::Borrow,
    error::Error,
    fmt::{Debug, Display},
    hash::Hash,
    ops::{Deref, DerefMut, Range},
};

use crate::context::FileId;

/// Represents a span in the parsed source of the Bauble context.
///
/// This type corresponds to the byte offset in a file of the first character and the byte offset
/// just past the last character.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Span {
    /// The offset to the first character covered by the span.
    pub start: usize,
    /// The offset to the delimiting character covered by the span (non-inclusive).
    pub end: usize,
    file: FileId,
}

impl From<Span> for FileId {
    fn from(value: Span) -> Self {
        value.file
    }
}

impl Span {
    #[allow(missing_docs)]
    pub fn new(file: impl Into<FileId>, range: Range<usize>) -> Self {
        Self {
            start: range.start,
            end: range.end,
            file: file.into(),
        }
    }

    /// This is equivalent to `self.end - self.start`.
    pub fn len(&self) -> usize {
        self.end - self.start
    }

    /// An empty span is when `self.start == self.end` or `self.len() == 0`
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.start == self.end
    }

    /// Creates a sub span of the current span.
    ///
    /// The subspan will be offset by the start of `self` and must exists within the bounds of `self`.
    ///
    /// # Panic
    ///
    /// This function will panic if `range.start` or `range.end` exists outside the bounds of `self`,
    /// that is to say, if `range.start` is greater or equal to `self.len()` or `range.end` is greater
    /// than `self.len()`.
    pub fn sub_span(&self, range: Range<usize>) -> Span {
        assert!(range.start < self.len());
        assert!(range.end <= self.len());
        Span {
            file: self.file,
            start: self.start + range.start,
            end: self.start + range.end,
        }
    }

    #[allow(missing_docs)]
    pub fn file(&self) -> FileId {
        self.file
    }
}

impl chumsky::span::Span for crate::Span {
    type Context = FileId;
    type Offset = usize;

    fn new(context: Self::Context, range: Range<Self::Offset>) -> Self {
        Self {
            start: range.start,
            end: range.end,
            file: context,
        }
    }
    fn context(&self) -> Self::Context {
        self.file
    }
    fn start(&self) -> Self::Offset {
        self.start
    }
    fn end(&self) -> Self::Offset {
        self.end
    }
}

impl ariadne::Span for Span {
    type SourceId = FileId;

    fn source(&self) -> &Self::SourceId {
        &self.file
    }

    fn start(&self) -> usize {
        self.start
    }

    fn end(&self) -> usize {
        self.end
    }
}

/// Represents a value associated with a span, meaning it is tied with some part of a Bauble source.
#[allow(missing_docs)]
#[derive(Clone, Copy)]
pub struct Spanned<T> {
    pub span: Span,
    pub value: T,
}

impl<T: PartialOrd> PartialOrd for Spanned<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.value.partial_cmp(&other.value)
    }
}

impl<T: Ord> Ord for Spanned<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.value.cmp(&other.value)
    }
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

#[allow(missing_docs)]
impl<T> Spanned<T> {
    pub fn new(span: Span, value: T) -> Self {
        Self { span, value }
    }

    pub fn as_ref(&self) -> Spanned<&T> {
        Spanned::new(self.span, &self.value)
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

impl<T: Error> Error for Spanned<T> {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        self.value.source()
    }
}

/// A helper trait for creating spanned values. It is implemented for all sized types.
pub trait SpanExt: Sized {
    /// Wraps `self` into a [`Spanned`] type.
    fn spanned(self, span: Span) -> Spanned<Self>;
}

impl<T: Sized> SpanExt for T {
    fn spanned(self, span: Span) -> Spanned<Self> {
        Spanned::new(span, self)
    }
}

impl<T: Borrow<str>> Borrow<str> for Spanned<T> {
    fn borrow(&self) -> &str {
        self.value.borrow()
    }
}
