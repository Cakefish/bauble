//! Provides helper functions for displaying Bauble values.

// NOTE(@docs) the display API is self-explanatory.
#![allow(missing_docs)]

use std::{borrow::Borrow, collections::HashMap};

use crate::{
    Spanned,
    parse::{ParseVal, ParseValues, PathTreeEnd, PathTreeNode, allowed_in_raw_literal},
    path::TypePath,
    types::{TypeKind, TypeRegistry},
};

use super::{Attributes, FieldsKind, Object, UnspannedVal, Val, Value, ValueContainer, ValueTrait};
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
        typed_context: bool,
    }

    pub struct LineWriter<'a, CTX>(Formatter<'a, CTX>);

    impl<'a, CTX> LineWriter<'a, CTX> {
        pub fn is_typed(&self) -> bool {
            self.0.is_typed()
        }
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

        pub fn with_typed_context(&mut self) -> LineWriter<CTX> {
            LineWriter(self.0.with_typed_context())
        }

        pub fn with_untyped_context(&mut self) -> LineWriter<CTX> {
            LineWriter(self.0.with_untyped_context())
        }
    }

    impl<'a, CTX> Formatter<'a, CTX> {
        pub fn is_typed(&self) -> bool {
            self.typed_context
        }

        pub fn start(config: &'a DisplayConfig, ctx: &'a CTX, string: &'a mut String) -> Self {
            Self {
                config,
                string,
                indent: 0,
                ctx,
                ty: "",
                typed_context: true,
            }
        }
        fn reborrow(&mut self) -> Formatter<CTX> {
            Formatter {
                config: self.config,
                string: self.string,
                indent: self.indent,
                ctx: self.ctx,
                ty: self.ty,
                typed_context: self.typed_context,
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
                typed_context: self.typed_context,
            }
        }

        pub fn with_typed_context(&mut self) -> Formatter<'_, CTX> {
            Formatter {
                config: self.config,
                string: self.string,
                indent: self.indent,
                ctx: self.ctx,
                ty: self.ty,
                typed_context: true,
            }
        }

        pub fn with_untyped_context(&mut self) -> Formatter<'_, CTX> {
            Formatter {
                config: self.config,
                string: self.string,
                indent: self.indent,
                ctx: self.ctx,
                ty: self.ty,
                typed_context: false,
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

impl<CTX: ValueCtx<V>, V: ValueTrait> IndentedDisplay<CTX> for Value<V>
where
    V::Ref: std::fmt::Display,
    V::Variant: std::fmt::Display,
    V::Field: std::fmt::Display,
    V::Inner: IndentedDisplay<CTX> + ValueContainer<ContainerField: std::fmt::Display>,
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
                super::PrimitiveValue::Default => w.write("default"),
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
                if inner.has_attributes() {
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

impl<CTX, V: IndentedDisplay<CTX> + ValueContainer> IndentedDisplay<CTX> for Attributes<V>
where
    V::ContainerField: std::fmt::Display,
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

        let typed = match w.ctx().types.key_type(self.ty).kind {
            TypeKind::Transparent(t) | TypeKind::Ref(t) => {
                !matches!(w.ctx().types.key_type(t).kind, TypeKind::Trait(_))
            }
            _ => true,
        };

        let path = w
            .ctx()
            .types
            .get_writable_path(self.ty)
            .unwrap_or_default()
            .to_owned();

        let mut w = w.with_type(path.as_str());

        if !w.is_typed()
            && !path.is_empty()
            && match w.ctx().types.key_type(self.ty).kind {
                TypeKind::Struct(_)
                | TypeKind::Enum { .. }
                | TypeKind::Or(_)
                | TypeKind::EnumVariant { .. } => false,
                TypeKind::Primitive(p) => w.ctx().types.primitive_type(p) == self.ty,
                _ => true,
            }
        {
            w.write("<");
            w.write_type();
            w.write("> ");
        }

        self.value.indented_display(if typed {
            w.with_typed_context()
        } else {
            w.with_untyped_context()
        });
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

        let typed = match w.ctx().types.key_type(*self.ty).kind {
            TypeKind::Transparent(t) | TypeKind::Ref(t) => {
                !matches!(w.ctx().types.key_type(t).kind, TypeKind::Trait(_))
            }
            _ => true,
        };

        let path = w
            .ctx()
            .types
            .get_writable_path(*self.ty)
            .unwrap_or_default()
            .to_owned();

        let mut w = w.with_type(path.as_str());

        if !w.is_typed()
            && !path.is_empty()
            && match w.ctx().types.key_type(*self.ty).kind {
                TypeKind::Struct(_)
                | TypeKind::Enum { .. }
                | TypeKind::Or(_)
                | TypeKind::EnumVariant { .. } => false,
                TypeKind::Primitive(p) => w.ctx().types.primitive_type(p) == *self.ty,
                _ => true,
            }
        {
            w.write("<");
            w.write_type();
            w.write("> ");
        }

        self.value.indented_display(if typed {
            w.with_typed_context()
        } else {
            w.with_untyped_context()
        });
    }
}

impl<CTX: ValueCtx<ParseVal>> IndentedDisplay<CTX> for ParseVal {
    fn indented_display(&self, mut w: LineWriter<CTX>) {
        if !self.attributes.is_empty() {
            self.attributes.indented_display(w.reborrow());
            w.write(" ");
        }

        let ty = self.ty.as_ref().map(|p| p.to_string());
        let mut w = w.with_type(ty.as_deref().unwrap_or(""));

        if self.ty.is_some() && !matches!(*self.value, Value::Struct(_) | Value::Or(_)) {
            w.write("<");
            w.write_type();
            w.write("> ");
        }

        self.value.indented_display(w);
    }
}

impl<CTX: ValueCtx<V>, V: IndentedDisplay<CTX> + ValueTrait> IndentedDisplay<CTX> for Object<V> {
    fn indented_display(&self, mut w: LineWriter<CTX>) {
        let Some((_, ident)) = self.object_path.get_end() else {
            return;
        };

        w.write(ident.as_str());

        if let Some(registry) = w.ctx().type_registry() {
            let ty = self.value.ty();
            // We can skip displaying the type path if the value hints what type it should be. This
            // is the case for non-flattened structs and enums, and primitive types.
            let can_skip_type = registry.is_primitive_type(ty)
                || match &registry.key_type(ty).kind {
                    TypeKind::Struct(_) => true,
                    TypeKind::Enum { variants } => {
                        if let Value::Enum(variant, _) = self.value.value()
                            && let Some(variant_ty) = variants.get(variant.borrow())
                        {
                            matches!(
                                registry.key_type(variant_ty).kind,
                                TypeKind::EnumVariant { .. }
                            )
                        } else {
                            false
                        }
                    }

                    _ => false,
                };

            if !can_skip_type && let Some(path) = registry.get_writable_path(ty) {
                let path = path.to_owned();
                w.write(": ");
                w.write(path.as_str());
            }
        }

        w.write(" = ");
        self.value.indented_display(w);
    }
}

struct ValueDisplayCtx<'a, V: ValueTrait> {
    inlined_refs: HashMap<TypePath<&'a str>, &'a V::Inner>,
    types: &'a TypeRegistry,
}

trait ValueCtx<V: ValueTrait> {
    fn inline(&self, path: &V::Ref) -> Option<&V::Inner>;

    fn type_registry(&self) -> Option<&TypeRegistry>;
}

impl ValueCtx<ParseVal> for () {
    fn inline(&self, _path: &crate::parse::Path) -> Option<&ParseVal> {
        None
    }

    fn type_registry(&self) -> Option<&TypeRegistry> {
        None
    }
}

impl ValueCtx<Val> for ValueDisplayCtx<'_, Val> {
    fn inline(&self, path: &TypePath) -> Option<&Val> {
        self.inlined_refs.get(path.as_str()).copied()
    }

    fn type_registry(&self) -> Option<&TypeRegistry> {
        Some(self.types)
    }
}

impl ValueCtx<UnspannedVal> for ValueDisplayCtx<'_, UnspannedVal> {
    fn inline(&self, path: &TypePath) -> Option<&UnspannedVal> {
        self.inlined_refs.get(path.as_str()).copied()
    }

    fn type_registry(&self) -> Option<&TypeRegistry> {
        Some(self.types)
    }
}

impl<V: ValueTrait<Inner = V> + for<'a> IndentedDisplay<ValueDisplayCtx<'a, V>>>
    IndentedDisplay<TypeRegistry> for [Object<V>]
where
    for<'a> ValueDisplayCtx<'a, V>: ValueCtx<V>,
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

impl<CTX: ValueCtx<ParseVal>> IndentedDisplay<CTX> for ParseValues {
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
