use core::fmt;

use crate::{SpanExt, spanned::Spanned, value::Ident};
use indexmap::IndexMap;

pub type Fields = IndexMap<Ident, ParseVal>;

pub type Use = Spanned<PathTreeNode>;

#[derive(Clone, Debug, PartialEq)]
pub enum PathEnd {
    /// path::*::ident
    WithIdent(Ident),
    /// path::ident
    Ident(Ident),
}

impl fmt::Display for PathEnd {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PathEnd::WithIdent(ident) => write!(f, "*::{ident}"),
            PathEnd::Ident(ident) => write!(f, "{ident}"),
        }
    }
}

#[derive(PartialEq, Clone)]
pub struct Path {
    pub leading: Spanned<Vec<Ident>>,
    pub last: Spanned<PathEnd>,
}

impl Path {
    pub fn as_ident(&self) -> Option<Spanned<&str>> {
        if let (true, PathEnd::Ident(ident)) = (self.leading.is_empty(), &self.last.value) {
            Some(ident.as_str().spanned(ident.span))
        } else {
            None
        }
    }

    pub fn last_ident(&self) -> Spanned<&str> {
        let (PathEnd::WithIdent(ident) | PathEnd::Ident(ident)) = &self.last.value;

        ident.as_ref().map(|s| s.as_str())
    }

    pub fn span(&self) -> crate::Span {
        crate::Span::new(self.last.span, self.leading.span.start..self.last.span.end)
    }
}

impl fmt::Display for Path {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for leading in self.leading.iter() {
            write!(f, "{leading}::")?;
        }
        write!(f, "{}", self.last)
    }
}

impl fmt::Debug for Path {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Self as fmt::Display>::fmt(self, f)
    }
}

#[derive(Debug)]
pub enum PathTreeEnd {
    Group(Vec<Use>),
    Everything,
    PathEnd(PathEnd),
}

#[derive(Debug)]
pub struct PathTreeNode {
    pub leading: Spanned<Vec<Ident>>,
    pub end: Spanned<PathTreeEnd>,
}

pub type Attributes = crate::value::Attributes<ParseVal>;
pub type Value = crate::Value<ParseVal, Path, Path>;

#[derive(Debug, Clone)]
pub struct ParseVal {
    pub ty: Option<Path>,
    pub attributes: Spanned<Attributes>,
    pub value: Spanned<Value>,
}

#[derive(Debug, Clone)]
pub struct Binding {
    pub type_path: Option<Path>,
    pub value: ParseVal,
}

#[derive(Debug)]
pub struct ParseValues {
    pub uses: Vec<Use>,
    pub values: IndexMap<Ident, Binding>,
    pub copies: IndexMap<Ident, Binding>,
}
