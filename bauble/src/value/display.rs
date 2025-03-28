use crate::{
    Spanned,
    parse::{ParseVal, ParseValues, PathTreeEnd, PathTreeNode, allowed_in_raw_literal},
    path::TypePath,
    types::TypeRegistry,
};

use super::{Attributes, CopyVal, FieldsKind, Object, Val, Value};
/// Config to be used when formatting bauble.
pub struct DisplayConfig {
    /// String inserted for tabs.
    pub tab: &'static str,
    /// If supported this will create inline comments printing the type paths of values.
    pub debug_types: bool,
}

impl Default for DisplayConfig {
    fn default() -> Self {
        Self {
            tab: "    ",
            debug_types: false,
        }
    }
}

/// Display something that implements `IndentedDisplay`.
pub fn display_formatted<CTX, V: IndentedDisplay<CTX> + ?Sized>(
    v: &V,
    ctx: &CTX,
    config: &DisplayConfig,
) -> String {
    let mut s = String::new();

    Formatter::start(config, ctx, &mut s).write_line(|l| v.indented_display(l));

    s
}

mod formatter {
    use std::fmt::Write;

    use super::DisplayConfig;

    pub struct Formatter<'a, CTX> {
        config: &'a DisplayConfig,
        string: &'a mut String,
        indent: usize,
        ctx: &'a CTX,
        ty: &'a str,
    }

    pub struct LineWriter<'a, CTX>(Formatter<'a, CTX>);

    impl<CTX> LineWriter<'_, CTX> {
        pub fn write(&mut self, s: &str) {
            self.0.string.push_str(s)
        }

        pub fn write_type(&mut self) {
            self.write(self.0.ty);
        }

        pub fn write_type_path(&mut self) {
            if !self.0.ty.is_empty() {
                self.write(self.0.ty);
                self.write("::");
            }
        }

        pub fn fmt(&mut self, v: impl std::fmt::Display) {
            write!(&mut self.0.string, "{v}").expect("Shouldn't fail");
        }

        pub fn debug_fmt(&mut self, v: impl std::fmt::Debug) {
            write!(&mut self.0.string, "{v:?}").expect("Shouldn't fail");
        }

        pub fn reborrow(&mut self) -> LineWriter<CTX> {
            LineWriter(self.0.reborrow())
        }

        pub fn write_recursive(&mut self, f: impl FnOnce(Formatter<CTX>)) {
            self.0.string.push('\n');
            f(self.0.bump_indent());
        }

        pub fn ctx(&self) -> &CTX {
            self.0.ctx()
        }

        pub fn config(&self) -> &DisplayConfig {
            self.0.config()
        }

        pub fn with_type<'b>(&'b mut self, ty: &'b str) -> LineWriter<'b, CTX> {
            LineWriter(self.0.with_type(ty))
        }
    }

    impl<'a, CTX> Formatter<'a, CTX> {
        pub fn start(config: &'a DisplayConfig, ctx: &'a CTX, string: &'a mut String) -> Self {
            Self {
                config,
                string,
                indent: 0,
                ctx,
                ty: "",
            }
        }
        fn reborrow(&mut self) -> Formatter<CTX> {
            Formatter {
                config: self.config,
                string: self.string,
                indent: self.indent,
                ctx: self.ctx,
                ty: self.ty,
            }
        }
        fn bump_indent(&mut self) -> Formatter<CTX> {
            let mut r = self.reborrow();
            r.indent += 1;
            r
        }
        pub fn with_type<'b>(&'b mut self, ty: &'b str) -> Formatter<'b, CTX> {
            let mut r = self.reborrow();
            r.ty = ty;
            r
        }
        pub fn write_line(&mut self, f: impl FnOnce(LineWriter<CTX>)) {
            for _ in 0..self.indent {
                self.string.push_str(self.config.tab);
            }

            f(LineWriter(self.reborrow()));

            self.string.push('\n');
        }

        pub fn ctx(&self) -> &CTX {
            self.ctx
        }

        pub fn config(&self) -> &DisplayConfig {
            self.config
        }
    }
}

use formatter::{Formatter, LineWriter};

pub trait IndentedDisplay<CTX> {
    fn indented_display(&self, w: LineWriter<CTX>);
}

fn slice_display<CTX, T: IndentedDisplay<CTX>>(slice: &[T], mut w: LineWriter<CTX>) {
    match slice {
        [] => {}
        [item] => item.indented_display(w),
        items => {
            w.write_recursive(|mut f| {
                for item in items {
                    f.write_line(|mut l| {
                        item.indented_display(l.reborrow());
                        l.write(",");
                    });
                }
            });
        }
    }
}

impl<CTX, Inner: IndentedDisplay<CTX>, Ref: std::fmt::Display, Variant: std::fmt::Display>
    IndentedDisplay<CTX> for Value<Inner, Ref, Variant>
{
    fn indented_display(&self, mut w: LineWriter<CTX>) {
        match self {
            Value::Ref(r) => {
                w.write("$");
                w.fmt(r);
            }
            Value::Tuple(items) => {
                w.write("(");
                slice_display(items, w.reborrow());
                w.write(")");
            }
            Value::Array(items) => {
                w.write("[");
                slice_display(items, w.reborrow());
                w.write("]");
            }
            Value::Map(items) => {
                w.write("{");
                if !items.is_empty() {
                    w.write_recursive(|mut f| {
                        for (key, value) in items {
                            f.write_line(|mut l| {
                                key.indented_display(l.reborrow());
                                l.write(": ");
                                value.indented_display(l.reborrow());
                                l.write(",");
                            });
                        }
                    });
                }
                w.write("}");
            }
            Value::Struct(fields_kind) => {
                w.write_type();
                match fields_kind {
                    FieldsKind::Unit => {}
                    FieldsKind::Unnamed(items) => {
                        w.write("(");
                        slice_display(items, w.reborrow());
                        w.write(")");
                    }
                    FieldsKind::Named(items) => {
                        w.write(" {");
                        if !items.is_empty() {
                            w.write_recursive(|mut f| {
                                for (field, value) in items {
                                    f.write_line(|mut l| {
                                        l.write(field.as_str());
                                        l.write(": ");
                                        value.indented_display(l.reborrow());
                                        l.write(",");
                                    });
                                }
                            });
                        }
                        w.write("}");
                    }
                }
            }
            Value::Or(or) => match or.as_slice() {
                [] => w.write("|"),
                [variant] => {
                    w.write_type_path();
                    w.fmt(variant);
                }
                [rest @ .., last] => {
                    for v in rest {
                        w.write_type_path();
                        w.fmt(v);
                        w.write(" | ");
                    }
                    w.fmt(last);
                }
            },
            Value::Primitive(primitive_value) => match primitive_value {
                super::PrimitiveValue::Num(v) => w.fmt(v),
                super::PrimitiveValue::Str(v) => w.debug_fmt(v),
                super::PrimitiveValue::Bool(v) => w.fmt(v),
                super::PrimitiveValue::Unit => w.write("()"),
                // `Raw` is a bit annoying to handle here, since we don't know how it
                // was originally expressed. So we need to check:
                // 1. Can it be displayed as a literal raw, i.e `#some_raw`
                // 2. If not, how many braces do we need, since raw values can contain
                //    `}`, but it has to end with as many `}` as there was `{` at the
                //    start.
                super::PrimitiveValue::Raw(v) => {
                    let mut num_braces = None;
                    let mut row = None;

                    let mut first = None;
                    let mut last = None;
                    for c in v.chars() {
                        if first.is_none() {
                            first = Some(c);
                        }
                        last = Some(c);
                        if num_braces.is_none() && !allowed_in_raw_literal(c) {
                            num_braces = Some(1);
                        }

                        if c == '}' {
                            *row.get_or_insert(0) += 1;
                        } else if let Some(r) = row {
                            let current = num_braces.get_or_insert(r + 1);
                            *current = (r + 1).max(*current);
                            row = None;
                        }
                    }

                    if let Some(n) = num_braces {
                        w.write("#");
                        for _ in 0..n {
                            w.write("{");
                        }
                        if first == Some('{') {
                            w.write(" ");
                        }
                        w.write(v);
                        if last == Some('}') {
                            w.write(" ");
                        }
                        for _ in 0..n {
                            w.write("}");
                        }
                    } else {
                        w.write("#");
                        w.write(v);
                    }
                }
            },
            Value::Transparent(inner) | Value::Enum(_, inner) => {
                w.write("(");
                inner.indented_display(w.reborrow());
                w.write(")");
            }
        }
    }
}

impl<CTX, Inner: IndentedDisplay<CTX>> IndentedDisplay<CTX> for Attributes<Inner> {
    fn indented_display(&self, mut w: LineWriter<CTX>) {
        match self.len() {
            0 => {}
            1 => {
                let (ident, val) = self.first().expect("We know length is 1");
                w.write("#[");
                w.write(ident);
                w.write(" = ");
                val.indented_display(w.reborrow());
                w.write("]")
            }
            _ => {
                w.write("#[");
                w.write_recursive(|mut f| {
                    for (ident, val) in self.iter() {
                        f.write_line(|mut w| {
                            w.write(ident);
                            w.write(" = ");
                            val.indented_display(w.reborrow());
                            w.write(",");
                        });
                    }
                });
                w.write("]")
            }
        }
    }
}

impl IndentedDisplay<TypeRegistry> for Val {
    fn indented_display(&self, mut w: LineWriter<TypeRegistry>) {
        if w.config().debug_types {
            w.write("/* ");
            let path = w.ctx().key_type(*self.ty).meta.path.clone();
            w.fmt(&path);
            w.write(" */ ");
        }

        if !self.attributes.is_empty() {
            self.attributes.indented_display(w.reborrow());
            w.write(" ");
        }

        let path = w
            .ctx()
            .get_writable_path(*self.ty)
            .unwrap_or_default()
            .to_owned();
        self.value.indented_display(w.with_type(path.as_str()));
    }
}

impl<CTX> IndentedDisplay<CTX> for ParseVal {
    fn indented_display(&self, mut w: LineWriter<CTX>) {
        if !self.attributes.is_empty() {
            self.attributes.indented_display(w.reborrow());
            w.write(" ");
        }

        let ty = self.ty.as_ref().map(|p| p.to_string());
        self.value
            .indented_display(w.with_type(ty.as_deref().unwrap_or("")));
    }
}

impl IndentedDisplay<TypeRegistry> for CopyVal {
    fn indented_display(&self, mut w: LineWriter<TypeRegistry>) {
        match self {
            CopyVal::Copy {
                ty,
                value,
                attributes,
            } => {
                let path = if let Some(ty) = ty {
                    if w.config().debug_types {
                        w.write("/* ");
                        let path = w.ctx().key_type(ty.value).meta.path.clone();
                        w.fmt(&path);
                        w.write(" */ ");
                    }

                    w.ctx()
                        .get_writable_path(ty.value)
                        .unwrap_or_default()
                        .to_owned()
                } else {
                    TypePath::empty()
                };

                if !attributes.is_empty() {
                    attributes.indented_display(w.reborrow());
                    w.write(" ");
                }

                value.indented_display(w.with_type(path.as_str()));
            }
            CopyVal::Resolved(val) => {
                val.indented_display(w);
            }
        }
    }
}

impl IndentedDisplay<TypeRegistry> for Object {
    fn indented_display(&self, mut w: LineWriter<TypeRegistry>) {
        let Some((_, ident)) = self.object_path.get_end() else {
            return;
        };

        w.write(ident.as_str());

        if let Some(path) = w.ctx().get_writable_path(*self.value.ty) {
            let path = path.to_owned();
            w.write(": ");
            w.write(path.as_str());
        }

        w.write(" = ");
        self.value.indented_display(w);
    }
}

impl IndentedDisplay<TypeRegistry> for [Object] {
    fn indented_display(&self, mut w: LineWriter<TypeRegistry>) {
        let mut iter = self.iter();

        if let Some(o) = iter.next() {
            o.indented_display(w.reborrow());
        }

        for o in iter {
            w.write("\n\n");
            o.indented_display(w.reborrow());
        }
    }
}

impl<CTX> IndentedDisplay<CTX> for PathTreeNode {
    fn indented_display(&self, mut w: LineWriter<CTX>) {
        for ident in self.leading.iter() {
            w.write(ident);
            w.write("::");
        }

        match &self.end.value {
            PathTreeEnd::Group(items) => {
                w.write("{");
                slice_display(items, w.reborrow());
                w.write("}");
            }
            PathTreeEnd::Everything => w.write("*"),
            PathTreeEnd::PathEnd(path_end) => match path_end {
                crate::parse::PathEnd::WithIdent(s) => {
                    w.write("*::");
                    w.write(s);
                }
                crate::parse::PathEnd::Ident(s) => w.write(s),
            },
        }
    }
}

impl<CTX, T: IndentedDisplay<CTX>> IndentedDisplay<CTX> for Spanned<T> {
    fn indented_display(&self, w: LineWriter<CTX>) {
        self.value.indented_display(w)
    }
}

impl<CTX> IndentedDisplay<CTX> for ParseValues {
    fn indented_display(&self, mut w: LineWriter<CTX>) {
        let mut written = false;
        for u in self.uses.iter() {
            u.indented_display(w.reborrow());
            w.write(";\n");
            written = true;
        }

        let mut iter = self.copies.iter();

        if let Some((ident, binding)) = iter.next() {
            if written {
                w.write("\n\n");
            }

            w.write("copy ");
            w.write(ident);
            if let Some(ty) = &binding.type_path {
                w.write(": ");
                w.fmt(ty);
            }
            w.write(" = ");
            binding.value.indented_display(w.reborrow());
        }

        for (ident, binding) in iter {
            w.write("\n\n");

            w.write("copy ");
            w.write(ident);
            if let Some(ty) = &binding.type_path {
                w.write(": ");
                w.fmt(ty);
            }
            w.write(" = ");
            binding.value.indented_display(w.reborrow());
        }

        let mut iter = self.values.iter();

        if let Some((ident, binding)) = iter.next() {
            if written {
                w.write("\n\n");
            }

            w.write(ident);
            if let Some(ty) = &binding.type_path {
                w.write(": ");
                w.fmt(ty);
            }
            w.write(" = ");
            binding.value.indented_display(w.reborrow());
        }

        for (ident, binding) in iter {
            w.write("\n\n");

            w.write(ident);
            if let Some(ty) = &binding.type_path {
                w.write(": ");
                w.fmt(ty);
            }
            w.write(" = ");
            binding.value.indented_display(w.reborrow());
        }
    }
}
