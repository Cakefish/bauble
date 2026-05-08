use core::fmt;

use crate::{
    SpanExt,
    spanned::{Span, Spanned},
    value::{AnyVal, Ident, SpannedValue, ValueTrait},
};
use indexmap::IndexMap;

#[derive(Clone, Debug, PartialEq)]
pub enum PathEnd {
    /// path::*::ident
    ///
    /// This refers to an item with the identifier `ident` in some path that starts with
    /// `path`. If multiple such paths exist within the same item namespace, an error will be
    /// generated.
    WithIdent(Ident),
    /// path::ident
    Ident(Ident),
    /// path::*::ident<...>
    WithIdentGeneric(Ident, Spanned<Box<Path>>),
    /// path::ident<...>
    IdentGeneric(Ident, Spanned<Box<Path>>),
}

impl fmt::Display for PathEnd {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PathEnd::WithIdent(ident) => write!(f, "*::{ident}"),
            PathEnd::Ident(ident) => write!(f, "{ident}"),
            PathEnd::WithIdentGeneric(ident, path) => write!(f, "*::{ident}<{path}>",),
            PathEnd::IdentGeneric(ident, path) => write!(f, "{ident}<{path}>",),
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
        let (PathEnd::WithIdent(ident)
        | PathEnd::Ident(ident)
        | PathEnd::IdentGeneric(ident, _)
        | PathEnd::WithIdentGeneric(ident, _)) = &self.last.value;

        ident.as_ref().map(|s| s.as_str())
    }

    pub fn span(&self) -> crate::Span {
        crate::Span::new(self.last.span, self.leading.span.start..self.last.span.end)
    }

    pub fn split_generic(&self) -> Option<(Path, &Path)> {
        match &*self.last {
            PathEnd::WithIdent(_) | PathEnd::Ident(_) => None,
            PathEnd::WithIdentGeneric(ident, path) => Some((
                Path {
                    leading: self.leading.clone(),
                    last: Spanned::new(self.last.span, PathEnd::WithIdent(ident.clone())),
                },
                path.as_ref().to_inner(),
            )),
            PathEnd::IdentGeneric(ident, path) => Some((
                Path {
                    leading: self.leading.clone(),
                    last: Spanned::new(self.last.span, PathEnd::Ident(ident.clone())),
                },
                path.as_ref().to_inner(),
            )),
        }
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
    /// Type known from the value (i.e. for struct types) or explicitly specified by prefixing the
    /// value with `<type>`.
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
    /// Type explicitly specified in the binding definition. This is the syntax where `: type`
    /// appears after the identifier before `=`.
    pub type_path: Option<Path>,
    pub value: ParseVal,
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub enum BindingIdent {
    /// This is the top level asset in a parsed file.
    ///
    /// It has the special cased identifier `0` and appears as the first item in the file.
    ///
    /// This holds no identifier string because it will have the same path as the file containing
    /// it.
    TopLevel(Spanned<()>),
    /// This is a local asset. I.e. any additional assets in a parsed file.
    Local(Ident),
}

impl BindingIdent {
    pub fn as_str(&self) -> &str {
        match self {
            Self::TopLevel(_) => crate::object_path::TOP_LEVEL_IDENTIFIER,
            Self::Local(ident) => ident,
        }
    }

    pub fn span(&self) -> Span {
        match self {
            Self::TopLevel(span) => span.span,
            Self::Local(ident) => ident.span,
        }
    }
}

#[derive(Debug)]
pub struct ParseValues {
    pub uses: Vec<Spanned<PathTreeNode>>,
    pub values: IndexMap<BindingIdent, Binding>,
}
