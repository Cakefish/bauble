use core::fmt;

use crate::{
    SpanExt,
    spanned::Spanned,
    value::{AnyVal, Ident, SpannedValue, ValueTrait},
};
use indexmap::IndexMap;

#[derive(Clone, Debug, PartialEq)]
pub enum PathEnd {
    // TODO: document how this syntax works?
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

impl std::borrow::Borrow<str> for Path {
    fn borrow(&self) -> &str {
        &self.last_ident()
    }
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
    Group(Vec<Spanned<PathTreeNode>>),
    Everything,
    PathEnd(PathEnd),
}

#[derive(Debug)]
pub struct PathTreeNode {
    pub leading: Spanned<Vec<Ident>>,
    pub end: Spanned<PathTreeEnd>,
}

#[derive(Debug, Clone)]
pub struct ParseVal {
    pub ty: Option<Path>,
    pub attributes: Spanned<crate::Attributes<ParseVal>>,
    pub value: Spanned<crate::Value<ParseVal>>,
}

impl ValueTrait for ParseVal {
    type Inner = Self;

    type Ref = Path;

    type Variant = Path;

    type Field = Ident;

    fn ty(&self) -> crate::types::TypeId {
        crate::types::TypeRegistry::any_type()
    }

    fn attributes(&self) -> &crate::Attributes<Self::Inner> {
        &self.attributes
    }

    fn value(&self) -> &crate::Value<Self> {
        &self.value
    }

    fn to_any(&self) -> AnyVal {
        AnyVal::Parse(self)
    }
}

impl SpannedValue for ParseVal {
    fn type_span(&self) -> crate::Span {
        self.ty
            .as_ref()
            .map(|s| s.span())
            .unwrap_or(self.value.span)
    }

    fn value_span(&self) -> crate::Span {
        self.value.span
    }

    fn attributes_span(&self) -> crate::Span {
        self.attributes.span
    }
}

#[derive(Debug, Clone)]
pub struct Binding {
    pub type_path: Option<Path>,
    pub value: ParseVal,
}

#[derive(Debug)]
pub struct ParseValues {
    pub uses: Vec<Spanned<PathTreeNode>>,
    pub values: IndexMap<Ident, Binding>,
    pub copies: IndexMap<Ident, Binding>,
}
