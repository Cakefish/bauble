use std::{collections::HashMap, hash::Hash};

use crate::{
    Spanned,
    parse::{ParseVal, ParseValues, PathTreeEnd, PathTreeNode, allowed_in_raw_literal},
    path::TypePath,
    types::{TypeId, TypeRegistry},
};

use super::{Attributes, FieldsKind, Ident, Object, UnspannedVal, Val, Value};
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

    impl<'a, CTX> LineWriter<'a, CTX> {
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
            f(self.0.bump_indent());
            self.0.new_line();
        }

        pub fn ctx(&self) -> &'a CTX {
            self.0.ctx()
        }

        pub fn config(&self) -> &DisplayConfig {
            self.0.config()
        }

        pub fn with_type<'b>(&'b mut self, ty: &'b str) -> LineWriter<'b, CTX> {
            LineWriter(self.0.with_type(ty))
        }

        pub fn with_ctx<'b, C>(&'b mut self, ctx: &'b C) -> LineWriter<'b, C> {
            LineWriter(self.0.with_ctx(ctx))
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
        pub fn with_ctx<'b, C>(&'b mut self, ctx: &'b C) -> Formatter<'b, C> {
            Formatter {
                config: self.config,
                string: self.string,
                indent: self.indent,
                ctx,
                ty: self.ty,
            }
        }

        fn new_line(&mut self) {
            self.string.push('\n');

            for _ in 0..self.indent {
                self.string.push_str(self.config.tab);
            }
        }

        // pub fn map_ctx<'b, C>(&'b mut self, c: impl FnOnce(&CTX) -> C)
        pub fn write_line(&mut self, f: impl FnOnce(LineWriter<CTX>)) {
            self.new_line();
            f(LineWriter(self.reborrow()));
        }

        pub fn ctx(&self) -> &'a CTX {
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

impl<
    CTX: ValueCtx<Inner, Ref = Ref, Field = Field>,
    Inner: IndentedDisplay<CTX>,
    Ref: std::fmt::Display,
    Variant: std::fmt::Display,
    Field: std::fmt::Display + Hash + Eq,
> IndentedDisplay<CTX> for Value<Inner, Ref, Variant, Field>
{
    fn indented_display(&self, mut w: LineWriter<CTX>) {
        match self {
            Value::Ref(r) => {
                if let Some(inline) = w.ctx().inline(r) {
                    inline.indented_display(w);
                } else {
                    w.write("$");
                    w.fmt(r);
                }
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
                                        l.fmt(field);
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
            Value::Transparent(inner) => {
                if !w.ctx().attributes(inner).is_empty() {
                    w.write("(");
                    inner.indented_display(w.reborrow());
                    w.write(")");
                } else {
                    inner.indented_display(w.reborrow());
                }
            }
            Value::Enum(_, inner) => {
                inner.indented_display(w.reborrow());
            }
        }
    }
}

impl<CTX, Inner: IndentedDisplay<CTX>, I: Hash + Eq + std::fmt::Display> IndentedDisplay<CTX>
    for Attributes<Inner, I>
{
    fn indented_display(&self, mut w: LineWriter<CTX>) {
        match self.len() {
            0 => {}
            1 => {
                let (ident, val) = self.first().expect("We know length is 1");
                w.write("#[");
                w.fmt(ident);
                w.write(" = ");
                val.indented_display(w.reborrow());
                w.write("]")
            }
            _ => {
                w.write("#[");
                w.write_recursive(|mut f| {
                    for (ident, val) in self.iter() {
                        f.write_line(|mut w| {
                            w.fmt(ident);
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

impl IndentedDisplay<ValueDisplayCtx<'_, UnspannedVal>> for UnspannedVal {
    fn indented_display(&self, mut w: LineWriter<ValueDisplayCtx<'_, UnspannedVal>>) {
        if w.config().debug_types {
            w.write("/* ");
            let path = w.ctx().types.key_type(self.ty).meta.path.clone();
            w.fmt(&path);
            w.write(" */ ");
        }

        if !self.attributes.is_empty() {
            self.attributes.indented_display(w.reborrow());
            w.write(" ");
        }

        let path = w
            .ctx()
            .types
            .get_writable_path(self.ty)
            .unwrap_or_default()
            .to_owned();
        self.value.indented_display(w.with_type(path.as_str()));
    }
}

impl IndentedDisplay<ValueDisplayCtx<'_, Val>> for Val {
    fn indented_display(&self, mut w: LineWriter<ValueDisplayCtx<'_, Val>>) {
        if w.config().debug_types {
            w.write("/* ");
            let path = w.ctx().types.key_type(*self.ty).meta.path.clone();
            w.fmt(&path);
            w.write(" */ ");
        }

        if !self.attributes.is_empty() {
            self.attributes.indented_display(w.reborrow());
            w.write(" ");
        }

        let path = w
            .ctx()
            .types
            .get_writable_path(*self.ty)
            .unwrap_or_default()
            .to_owned();
        self.value.indented_display(w.with_type(path.as_str()));
    }
}

impl<CTX: ValueCtx<ParseVal, Ref = crate::parse::Path, Field = Ident>> IndentedDisplay<CTX>
    for ParseVal
{
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

impl<CTX: ValueCtx<Inner>, Inner: IndentedDisplay<CTX>> IndentedDisplay<CTX> for Object<Inner> {
    fn indented_display(&self, mut w: LineWriter<CTX>) {
        let Some((_, ident)) = self.object_path.get_end() else {
            return;
        };

        w.write(ident.as_str());

        let ty = w.ctx().ty(&self.value);
        if let Some(path) = w.ctx().get_writable_path(ty) {
            let path = path.to_owned();
            w.write(": ");
            w.write(path.as_str());
        }

        w.write(" = ");
        self.value.indented_display(w);
    }
}

struct ValueDisplayCtx<'a, Inner> {
    inlined_refs: HashMap<TypePath<&'a str>, &'a Inner>,
    types: &'a TypeRegistry,
}

trait ValueCtx<Inner> {
    type Ref;
    type Field: Hash + Eq;
    fn inline(&self, path: &Self::Ref) -> Option<&Inner>;

    fn attributes<'a>(&self, val: &'a Inner) -> &'a Attributes<Inner, Self::Field>;

    fn ty(&self, val: &Inner) -> TypeId;

    fn get_writable_path(&self, _ty: TypeId) -> Option<TypePath<&str>> {
        None
    }
}

impl ValueCtx<ParseVal> for () {
    type Ref = crate::parse::Path;
    type Field = Ident;

    fn inline(&self, _path: &crate::parse::Path) -> Option<&ParseVal> {
        None
    }

    fn attributes<'a>(&self, val: &'a ParseVal) -> &'a Attributes<ParseVal> {
        &val.attributes
    }

    fn ty(&self, _val: &ParseVal) -> TypeId {
        TypeRegistry::any_type()
    }
}

impl ValueCtx<Val> for ValueDisplayCtx<'_, Val> {
    type Ref = TypePath;
    type Field = Ident;

    fn inline(&self, path: &TypePath) -> Option<&Val> {
        self.inlined_refs.get(path.as_str()).copied()
    }

    fn attributes<'a>(&self, val: &'a Val) -> &'a Attributes<Val> {
        &val.attributes
    }

    fn ty(&self, val: &Val) -> TypeId {
        *val.ty
    }

    fn get_writable_path(&self, ty: TypeId) -> Option<TypePath<&str>> {
        self.types.get_writable_path(ty)
    }
}

impl ValueCtx<UnspannedVal> for ValueDisplayCtx<'_, UnspannedVal> {
    type Ref = TypePath;
    type Field = String;

    fn inline(&self, path: &TypePath) -> Option<&UnspannedVal> {
        self.inlined_refs.get(path.as_str()).copied()
    }

    fn attributes<'a>(&self, val: &'a UnspannedVal) -> &'a Attributes<UnspannedVal, Self::Field> {
        &val.attributes
    }

    fn ty(&self, val: &UnspannedVal) -> TypeId {
        val.ty
    }

    fn get_writable_path(&self, ty: TypeId) -> Option<TypePath<&str>> {
        self.types.get_writable_path(ty)
    }
}

impl<Inner: for<'a> IndentedDisplay<ValueDisplayCtx<'a, Inner>>> IndentedDisplay<TypeRegistry>
    for [Object<Inner>]
where
    for<'a> ValueDisplayCtx<'a, Inner>: ValueCtx<Inner>,
{
    fn indented_display(&self, mut w: LineWriter<TypeRegistry>) {
        let mut inlined_refs = HashMap::new();
        let mut written = Vec::new();
        for object in self.iter() {
            if object.object_path.is_writable() {
                written.push(object);
            } else {
                inlined_refs.insert(object.object_path.borrow(), &object.value);
            }
        }
        let ctx = ValueDisplayCtx {
            inlined_refs,
            types: w.ctx(),
        };
        let mut w = w.with_ctx(&ctx);
        let mut iter = written.into_iter();

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

impl<CTX: ValueCtx<ParseVal, Ref = crate::parse::Path, Field = Ident>> IndentedDisplay<CTX>
    for ParseValues
{
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
