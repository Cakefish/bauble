use core::fmt;

use crate::spanned::{Span, SpanExt, Spanned};
use indexmap::IndexMap;
use rust_decimal::Decimal;

// Could maybe use `&str`?
pub type Ident = Spanned<String>;

pub type Map = Vec<(Object, Object)>;

pub type Fields = IndexMap<Ident, Object>;

pub type Sequence = Vec<Object>;

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
    pub fn is_just(&self, s: &str) -> bool {
        self.leading.is_empty()
            && match &self.last.value {
                PathEnd::WithIdent(_) => false,
                PathEnd::Ident(ident) => ident.as_str() == s,
            }
    }

    pub fn as_ident(&self) -> Option<&str> {
        if let (true, PathEnd::Ident(ident)) = (self.leading.is_empty(), &self.last.value) {
            Some(ident.as_str())
        } else {
            None
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

impl Path {
    pub fn join(&mut self, part: Ident) -> bool {
        match &mut self.last.value {
            PathEnd::WithIdent(_) => false,
            PathEnd::Ident(ident) => {
                self.leading.push(std::mem::replace(ident, part));
                true
            }
        }
    }
}

#[derive(Debug, Clone)]
pub enum Value {
    Unit,
    Num(Decimal),
    Bool(bool),
    Str(String),
    Ref(Spanned<Path>),

    Path(Spanned<Path>),

    Map(Map),
    Struct {
        name: Option<Spanned<Path>>,
        fields: Fields,
    },
    Tuple {
        name: Option<Spanned<Path>>,
        fields: Sequence,
    },
    Array(Sequence),
    Or(Vec<Spanned<Path>>),
    Raw(String),

    Error,
}

// Is 3 spaces intended?
const TAB: &str = "   ";
impl Value {
    fn indented_display(&self, indent: usize, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let i = TAB.repeat(indent);
        match self {
            Value::Unit => write!(f, "()"),
            Value::Num(n) => write!(f, "{n}"),
            Value::Bool(n) => write!(f, "{n}"),
            Value::Str(n) => write!(f, "\"{n}\""),
            Value::Ref(n) => write!(f, "${n}"),
            Value::Path(n) => write!(f, "{n}"),

            Value::Struct { name, fields } => {
                writeln!(
                    f,
                    "{}{{",
                    match name {
                        Some(name) => format!("{name} "),
                        None => String::default(),
                    }
                )?;
                for (ident, object) in fields {
                    write!(f, "{i}{TAB}{}: ", ident.as_str())?;
                    object.indented_display(indent + 1, f)?;
                    writeln!(f, ",")?;
                }
                write!(f, "{i}}}")
            }
            Value::Map(s) => {
                writeln!(f, "{{")?;
                for (key, object) in s {
                    write!(f, "{i}{TAB}",)?;
                    key.indented_display(indent + 1, f)?;
                    write!(f, ": ")?;
                    object.indented_display(indent + 1, f)?;
                    writeln!(f, ",")?;
                }
                write!(f, "{i}}}")
            }
            Value::Tuple { name, fields } => {
                writeln!(
                    f,
                    "{}(\n",
                    match name {
                        Some(name) => format!("{name}"),
                        None => String::default(),
                    }
                )?;
                for object in fields {
                    write!(f, "{i}{TAB}")?;
                    object.indented_display(indent + 1, f)?;
                    writeln!(f, ",")?;
                }
                write!(f, "{i})")
            }
            Value::Array(s) => {
                writeln!(f, "[")?;
                for object in s {
                    write!(f, "{i}{TAB}")?;
                    object.indented_display(indent + 1, f)?;
                    writeln!(f, ",\n")?;
                }
                write!(f, "{i}]")
            }
            Value::Or(s) => {
                if s.is_empty() {
                    Ok(())
                } else {
                    let mut iter = s.iter();
                    write!(f, "{}", iter.next().unwrap())?;

                    if iter.len() == 1 {
                        write!(f, " | {}", iter.next().unwrap())
                    } else {
                        for path in iter {
                            write!(f, "\n{i}{TAB}| {path}")?;
                        }
                        Ok(())
                    }
                }
            }
            Value::Raw(s) => {
                write!(f, "@{{")?;
                let mut lines = s.lines();
                writeln!(f, "{}", lines.next().unwrap_or(""))?;
                for line in lines {
                    writeln!(f, "{i}{line}")?;
                }
                write!(f, "{i}}}")
            }

            Value::Error => write!(f, "Error"),
        }?;
        write!(f, " <{}>", self.ty())
    }

    fn ty(&self) -> &'static str {
        match self {
            Value::Unit => "unit",
            Value::Num(_) => "num",
            Value::Bool(_) => "bool",
            Value::Str(_) => "string",
            Value::Ref(_) => "ref",
            Value::Path(_) => "path",
            Value::Map(_) => "map",
            Value::Struct { .. } => "struct",
            Value::Tuple { .. } => "tuple",
            Value::Array(_) => "arr",
            Value::Or(_) => "or",
            Value::Raw(_) => "raw",
            Value::Error => "error",
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.indented_display(0, f)
    }
}

#[derive(Debug)]
pub enum PathTreeEnd {
    Group(Vec<Use>),
    Everything,
    PathEnd(PathEnd),
}

impl PathTreeEnd {
    fn indented_display(&self, indent: usize, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PathTreeEnd::Group(group) => {
                let i = TAB.repeat(indent);
                write!(f, "{{\n{i}")?;

                for node in group.iter() {
                    write!(f, "{TAB}")?;
                    node.indented_display(indent + 1, f)?;
                    write!(f, ",\n{i}")?;
                }

                write!(f, "}}")
            }
            PathTreeEnd::Everything => write!(f, "*"),
            PathTreeEnd::PathEnd(end) => write!(f, "{end}"),
        }
    }
}

#[derive(Debug)]
pub struct PathTreeNode {
    pub leading: Spanned<Vec<Ident>>,
    pub end: Spanned<PathTreeEnd>,
}

impl PathTreeNode {
    fn indented_display(&self, indent: usize, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for leading in self.leading.iter() {
            write!(f, "{leading}::")?;
        }

        self.end.indented_display(indent, f)
    }
}

#[derive(Clone, Debug, Default)]
pub struct Attributes(pub IndexMap<Ident, Object>);

impl Attributes {
    fn indented_display(&self, indent: usize, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self(attributes) = self;

        for (ident, value) in attributes.iter() {
            let i = TAB.repeat(indent);
            write!(f, "{i}#[{} = ", ident.as_str())?;
            value.indented_display(indent + 1, f)?;
            writeln!(f, "]")?;
        }

        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct Object {
    pub attributes: Spanned<Attributes>,
    pub value: Spanned<Value>,
}

impl Object {
    pub fn error(span: Span) -> Self {
        Self {
            attributes: Attributes::default().empty(),
            value: Value::Error.span(span),
        }
    }
}

impl Object {
    fn indented_display(&self, indent: usize, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.attributes.indented_display(indent, f)?;

        self.value.indented_display(indent, f)
    }
}

fn indented_display_value(
    ident: &Ident,
    object: &Object,
    indent: usize,
    f: &mut fmt::Formatter<'_>,
) -> fmt::Result {
    let i = TAB.repeat(indent);
    let mut first = true;
    if !object.attributes.0.is_empty() {
        first = false;
        object.attributes.indented_display(indent, f)?;
    }

    if !first {
        write!(f, "{i}")?;
    }

    write!(f, "{ident} = ")?;
    object.value.indented_display(indent, f)
}

#[derive(Debug)]
pub struct Values {
    pub uses: Vec<Use>,
    pub values: IndexMap<Ident, Object>,
    pub copies: IndexMap<Ident, Object>,
}

impl Values {
    fn indented_display(&self, indent: usize, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let i = TAB.repeat(indent);
        for use_item in self.uses.iter() {
            write!(f, "{i}use ")?;
            use_item.indented_display(indent, f)?;
            writeln!(f, ";\n")?;
        }

        for (ident, object) in self.values.iter() {
            indented_display_value(ident, object, indent, f)?;
            writeln!(f, "\n")?;
        }

        for (ident, object) in self.copies.iter() {
            write!(f, "{i}copy ")?;
            indented_display_value(ident, object, indent, f)?;
            writeln!(f, "\n")?;
        }

        Ok(())
    }
}

impl fmt::Display for Values {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.indented_display(0, f)
    }
}
