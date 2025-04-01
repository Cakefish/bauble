use std::{
    collections::{HashMap, HashSet},
    hash::Hash,
};

use indexmap::IndexMap;
use rust_decimal::Decimal;
use symbols::RefCopy;

use crate::{
    BaubleErrors, FileId, VariantKind,
    context::PathReference,
    parse::{ParseVal, ParseValues, Path, PathEnd},
    path::{TypePath, TypePathElem},
    spanned::{SpanExt, Spanned},
    types::{self, TypeId},
};

mod convert;
mod display;
mod error;
mod symbols;

use convert::{ConvertMeta, ConvertValue, no_attr, value_type};
pub use display::{DisplayConfig, IndentedDisplay, display_formatted};
use error::Result;
pub use error::{ConversionError, RefError, RefKind};
pub(crate) use symbols::Symbols;

#[derive(Clone, Debug, PartialEq)]
pub struct Attributes<Inner = Val, I: Hash + Eq = Ident>(IndexMap<I, Inner>);

impl<Inner, I: Hash + Eq> From<IndexMap<I, Inner>> for Attributes<Inner, I> {
    fn from(value: IndexMap<I, Inner>) -> Self {
        Self(value)
    }
}

impl<T, I: Hash + Eq> Default for Attributes<T, I> {
    fn default() -> Self {
        Self(Default::default())
    }
}

impl<T, I: Hash + Eq> Attributes<T, I> {
    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn get(&self, s: &str) -> Option<(&I, &T)>
    where
        str: indexmap::Equivalent<I>,
    {
        self.0.get_key_value(s)
    }

    pub fn values(&self) -> impl ExactSizeIterator<Item = &T> {
        self.0.values()
    }

    pub fn iter(&self) -> impl ExactSizeIterator<Item = (&I, &T)> {
        self.0.iter()
    }

    pub fn first(&self) -> Option<(&I, &T)> {
        self.0.first()
    }

    pub fn insert(&mut self, ident: I, v: T) {
        self.0.insert(ident, v);
    }

    pub fn take(&mut self, ident: &str) -> Option<T>
    where
        str: indexmap::Equivalent<I>,
    {
        self.0.swap_remove(ident)
    }
}

impl<T> IntoIterator for Attributes<T> {
    type Item = (Ident, T);

    type IntoIter = <IndexMap<Ident, T> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a, T> IntoIterator for &'a Attributes<T> {
    type Item = (&'a Ident, &'a T);

    type IntoIter = indexmap::map::Iter<'a, Ident, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

#[derive(Clone, Debug, PartialEq)]
/// A value with attributes
pub struct Val {
    pub ty: Spanned<TypeId>,
    pub value: Spanned<Value>,
    pub attributes: Spanned<Attributes>,
}

impl Val {
    pub fn into_unspanned(self) -> UnspannedVal {
        UnspannedVal {
            ty: *self.ty,
            value: match self.value.value {
                Value::Ref(r) => Value::Ref(r),
                Value::Tuple(seq) => {
                    Value::Tuple(seq.into_iter().map(|v| v.into_unspanned()).collect())
                }
                Value::Array(seq) => {
                    Value::Array(seq.into_iter().map(|v| v.into_unspanned()).collect())
                }
                Value::Map(map) => Value::Map(
                    map.into_iter()
                        .map(|(k, v)| (k.into_unspanned(), v.into_unspanned()))
                        .collect(),
                ),
                Value::Struct(fields) => Value::Struct(match fields {
                    FieldsKind::Unit => FieldsKind::Unit,
                    FieldsKind::Unnamed(fields) => FieldsKind::Unnamed(
                        fields.into_iter().map(|v| v.into_unspanned()).collect(),
                    ),
                    FieldsKind::Named(fields) => FieldsKind::Named(
                        fields
                            .into_iter()
                            .map(|(f, v)| (f.value, v.into_unspanned()))
                            .collect(),
                    ),
                }),
                Value::Or(items) => Value::Or(items.into_iter().map(|v| v.value).collect()),
                Value::Primitive(prim) => Value::Primitive(prim),
                Value::Transparent(inner) => Value::Transparent(Box::new(inner.into_unspanned())),
                Value::Enum(variant, inner) => {
                    Value::Enum(variant.value, Box::new(inner.into_unspanned()))
                }
            },
            attributes: Attributes(
                self.attributes
                    .value
                    .0
                    .into_iter()
                    .map(|(s, v)| (s.value, v.into_unspanned()))
                    .collect(),
            ),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct UnspannedVal {
    pub ty: TypeId,
    pub value: Value<UnspannedVal, TypePath, TypePathElem, String>,
    pub attributes: Attributes<UnspannedVal, String>,
}

impl UnspannedVal {
    /// Create a new unspanned val.
    ///
    /// In contexts where you have a `TypeRegistry`, for example in `Bauble::construct_type`,
    /// prefer using `TypeRegistry::instantiate` to construct this for types for which
    /// `TypeId` is known.
    pub fn new(value: Value<UnspannedVal, TypePath, TypePathElem, String>) -> Self {
        Self {
            ty: types::TypeRegistry::any_type(),
            value,
            attributes: Attributes::default(),
        }
    }

    pub fn with_type(mut self, ty: TypeId) -> Self {
        self.ty = ty;
        self
    }

    pub fn with_attribute(mut self, ty: TypeId) -> Self {
        self.ty = ty;
        self
    }
}

#[derive(Clone, Debug)]
enum CopyVal {
    Copy {
        ty: Option<Spanned<TypeId>>,
        value: Spanned<Value<CopyVal>>,
        attributes: Spanned<Attributes<CopyVal>>,
    },
    Resolved(Val),
}

impl CopyVal {
    fn span(&self) -> crate::Span {
        match self {
            CopyVal::Copy {
                value, attributes, ..
            } => crate::Span::new(value.span, attributes.span.start..value.span.end),
            CopyVal::Resolved(val) => val.span(),
        }
    }
}

impl Val {
    pub fn span(&self) -> crate::Span {
        crate::Span::new(
            self.value.span,
            self.attributes.span.start..self.value.span.end,
        )
    }
}

pub type Ident = Spanned<String>;

pub type Map<Inner = Val> = Vec<(Inner, Inner)>;

pub type Fields<Inner = Val, Field = Ident> = IndexMap<Field, Inner>;

pub type Sequence<Inner = Val> = Vec<Inner>;

#[derive(Clone, Debug, PartialEq)]
pub enum FieldsKind<Inner = Val, Field: Hash + Eq = Ident> {
    Unit,
    Unnamed(Sequence<Inner>),
    Named(Fields<Inner, Field>),
}

impl FieldsKind {
    pub fn variant_kind(&self) -> VariantKind {
        match self {
            FieldsKind::Unit => VariantKind::Path,
            FieldsKind::Unnamed(_) => VariantKind::Tuple,
            FieldsKind::Named(_) => VariantKind::Struct,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum PrimitiveValue {
    Num(Decimal),
    Str(String),
    Bool(bool),
    Unit,
    Raw(String),
}

#[derive(Clone, Debug, PartialEq)]
pub enum Value<
    Inner = Val,
    AssetRef = TypePath,
    Variant = Spanned<TypePathElem>,
    Field: Hash + Eq = Ident,
> {
    // Fully resolved path.
    Ref(AssetRef),

    Tuple(Sequence<Inner>),
    Array(Sequence<Inner>),
    Map(Map<Inner>),

    /// Either struct or enum variant
    Struct(FieldsKind<Inner, Field>),

    Or(Vec<Variant>),

    Primitive(PrimitiveValue),

    Transparent(Box<Inner>),

    Enum(Variant, Box<Inner>),
}

impl<T, P, I> Value<T, P, I> {
    pub fn primitive_type(&self) -> Option<types::Primitive> {
        match self {
            Self::Primitive(p) => Some(match p {
                PrimitiveValue::Num(_) => types::Primitive::Num,
                PrimitiveValue::Str(_) => types::Primitive::Str,
                PrimitiveValue::Bool(_) => types::Primitive::Bool,
                PrimitiveValue::Unit => types::Primitive::Unit,
                PrimitiveValue::Raw(_) => types::Primitive::Raw,
            }),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Object<Inner = Val> {
    pub object_path: TypePath,
    pub value: Inner,
}

impl Object<Val> {
    pub fn into_unspanned(self) -> Object<UnspannedVal> {
        Object {
            object_path: self.object_path,
            value: self.value.into_unspanned(),
        }
    }
}

#[derive(Clone, Debug)]
pub enum PathKind {
    Direct(TypePath),
    /// TypePath::*::TypePathElem
    Indirect(TypePath, TypePathElem),
}

impl std::fmt::Display for PathKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PathKind::Direct(path) => write!(f, "{path}"),
            PathKind::Indirect(path, ident) => write!(f, "{path}::*::{ident}"),
        }
    }
}

impl PathKind {
    fn could_be(&self, path: TypePath<&str>) -> bool {
        match self {
            PathKind::Direct(p) => p.borrow() == path,
            PathKind::Indirect(leading, ident) => {
                path.starts_with(leading.borrow())
                    && path.ends_with(*ident.borrow())
                    // If `leading` ends with `ident` we could have false positives if we didn't include this check.
                    && path.byte_len() > leading.byte_len() + ident.byte_len()
            }
        }
    }
}

/// We can delay registering `Ref` assets if what they're referencing hasn't been loaded yet.
pub struct DelayedRegister {
    pub asset: Spanned<TypePath>,
    pub reference: Spanned<PathKind>,
}

pub(crate) fn resolve_delayed(
    mut delayed: Vec<DelayedRegister>,
    ctx: &mut crate::context::BaubleContext,
) -> std::result::Result<(), Vec<Spanned<ConversionError>>> {
    loop {
        let old_len = delayed.len();

        // Try to register delayed registers, and remove them as they succeed.
        delayed.retain(|d| {
            if let Some(r) = match &d.reference.value {
                PathKind::Direct(path) => ctx.get_ref(path.borrow()),
                PathKind::Indirect(path, ident) => {
                    ctx.ref_with_ident(path.borrow(), ident.borrow())
                }
            } && let Some((ty, _)) = &r.asset
            {
                ctx.register_asset(d.asset.value.borrow(), *ty);
                false
            } else {
                true
            }
        });

        if delayed.is_empty() {
            return Ok(());
        }

        // If the length didn't change we have errors.
        if delayed.len() == old_len {
            let mut graph = petgraph::graphmap::DiGraphMap::new();
            let mut map = HashMap::new();
            for a in delayed.iter() {
                let node_a = graph.add_node(a.asset.as_ref().map(|p| p.borrow()));
                map.insert(node_a, a.reference.as_ref());

                for b in delayed.iter() {
                    if a.reference.could_be(b.asset.borrow()) {
                        graph.add_edge(node_a, b.asset.as_ref().map(|p| p.borrow()), ());
                    }
                }
            }

            let mut errors = Vec::new();
            for scc in petgraph::algo::tarjan_scc(&graph) {
                if scc.len() == 1 {
                    if map[&scc[0]].could_be(scc[0].borrow()) {
                        errors.push(
                            ConversionError::Cycle(vec![(
                                scc[0].to_string().spanned(scc[0].span),
                                vec![map[&scc[0]].to_string().spanned(map[&scc[0]].span)],
                            )])
                            .spanned(scc[0].span),
                        )
                    } else {
                        errors.push(
                            ConversionError::RefError(Box::new(RefError {
                                // TODO: Could pass uses here for better suggestions.
                                uses: None,
                                path: map[&scc[0]].value.clone(),
                                path_ref: PathReference::empty(),
                                kind: RefKind::Asset,
                            }))
                            .spanned(map[&scc[0]].span),
                        )
                    }
                } else {
                    errors.push(
                        ConversionError::Cycle(
                            scc.iter()
                                .map(|s| {
                                    (
                                        s.to_string().spanned(s.span),
                                        vec![map[s].to_string().spanned(map[s].span)],
                                    )
                                })
                                .collect(),
                        )
                        .spanned(scc[0].span),
                    );
                }
            }

            return Err(errors);
        }
    }
}

pub(crate) fn register_assets(
    path: TypePath<&str>,
    ctx: &mut crate::context::BaubleContext,
    default_uses: impl IntoIterator<Item = (TypePathElem, PathReference)>,
    values: &ParseValues,
) -> std::result::Result<Vec<DelayedRegister>, Vec<Spanned<ConversionError>>> {
    let mut uses = default_uses
        .into_iter()
        .map(|(key, val)| (key, RefCopy::Ref(val)))
        .collect();
    let mut errors = Vec::new();
    let mut delayed = Vec::new();

    let mut symbols = Symbols { ctx: &*ctx, uses };
    for use_ in &values.uses {
        if let Err(e) = symbols.add_use(use_) {
            errors.push(e);
        }
    }

    Symbols { uses, .. } = symbols;

    // TODO: Register these in a correct order to allow for assets referencing assets.
    for (ident, binding) in &values.values {
        let span = ident.span;
        let ident = &TypePathElem::new(ident.as_str()).expect("Invariant");
        let path = path.join(ident);
        let mut symbols = Symbols { ctx: &*ctx, uses };

        let ty = if let Some(ty) = &binding.type_path {
            symbols.resolve_type(ty)
        } else {
            let res = value_type(&binding.value, &symbols)
                .map(|v| {
                    convert::default_value_type(
                        &symbols,
                        binding.value.value.value.primitive_type(),
                        v,
                    )
                })
                .transpose()
                .unwrap_or(Err(
                    ConversionError::UnresolvedType.spanned(binding.value.value.span)
                ))
                .and_then(|v| {
                    if ctx.type_registry().key_type(v).kind.instanciable() {
                        Ok(v)
                    } else {
                        Err(ConversionError::UnresolvedType.spanned(binding.value.value.span))
                    }
                });

            if res.is_err()
                && let Value::Ref(reference) = &binding.value.value.value
                && let Ok(reference) = symbols.resolve_path(reference)
            {
                delayed.push(DelayedRegister {
                    asset: path.spanned(span),
                    reference,
                });
                Symbols { uses, .. } = symbols;
                continue;
            }

            res
        };

        match ty {
            Ok(ty) => {
                if let Err(e) = symbols.add_ref(
                    ident.to_owned(),
                    PathReference {
                        ty: None,
                        asset: Some((ty, path.clone())),
                        module: None,
                    },
                ) {
                    errors.push(e.spanned(binding.value.value.span));
                }
                Symbols { uses, .. } = symbols;
                ctx.register_asset(path.borrow(), ty);
            }
            Err(err) => {
                Symbols { uses, .. } = symbols;
                errors.push(err)
            }
        };
    }

    if errors.is_empty() {
        Ok(delayed)
    } else {
        Err(errors)
    }
}

pub(crate) fn convert_values(
    file: FileId,
    values: ParseValues,
    default_symbols: &Symbols,
) -> std::result::Result<Vec<Object>, BaubleErrors> {
    let mut use_symbols = Symbols::new(default_symbols.ctx);
    let mut use_errors = Vec::new();
    for use_ in values.uses {
        if let Err(e) = use_symbols.add_use(&use_) {
            use_errors.push(e);
        }
    }

    let mut symbols = default_symbols.clone();

    let path = symbols.ctx.get_file_path(file);

    for (symbol, _) in &values.values {
        let ident = TypePathElem::new(symbol.as_str()).expect("Invariant");
        let path = path.join(&ident);

        if let Some(PathReference {
            asset: Some(asset), ..
        }) = symbols.ctx.get_ref(path.borrow())
        {
            if let Err(e) = symbols.add_ref(
                ident.to_owned(),
                PathReference {
                    ty: None,
                    asset: Some(asset),
                    module: None,
                },
            ) {
                use_errors.push(e.spanned(symbol.span));
            }
        } else {
            // Didn't pre-register assets.
            use_errors.push(ConversionError::UnregisteredAsset.spanned(symbol.span));
        }
    }

    symbols.add(use_symbols);

    for (symbol, _) in &values.copies {
        let span = symbol.span;
        let symbol = match TypePathElem::new(symbol.as_str()).map_err(|e| e.spanned(span)) {
            Ok(s) => s,
            Err(e) => {
                use_errors.push(e.into());
                continue;
            }
        };
        symbols.uses.insert(symbol.to_owned(), RefCopy::Unresolved);
    }

    let mut spans = HashMap::new();
    let mut contained_spans =
        HashMap::<TypePathElem<&str>, Vec<Spanned<TypePathElem<&str>>>>::new();
    let mut copy_graph = petgraph::graphmap::DiGraphMap::new();

    for (symbol, value) in &values.copies {
        let span = symbol.span;
        let symbol = match TypePathElem::new(symbol.as_str()).map_err(|e| e.spanned(span)) {
            Ok(s) => s,
            Err(e) => {
                use_errors.push(e.into());
                continue;
            }
        };

        spans.insert(symbol, span);
        copy_graph.add_node(symbol);
        find_copy_refs(&value.value, &symbols, &mut |s| {
            copy_graph.add_edge(symbol, s.value, ());
            contained_spans.entry(symbol).or_default().push(s);
        });
    }

    let mut objects = Vec::new();
    let mut name_allocs = HashMap::new();
    let mut add_value = |name: TypePathElem<&str>, val: Val, symbols: &Symbols| {
        let idx = *name_allocs
            .entry(name.to_owned())
            .and_modify(|i| *i += 1u64)
            .or_insert(0);
        let name = TypePathElem::new(format!("{name}@{idx}"))
            .expect("idx is just a number, and we know name is a valid path elem.");

        objects.push(create_object(path, name.borrow(), val, symbols)?);

        Ok(Value::Ref(path.join(&name)))
    };

    let mut node_removals = Vec::new();
    for scc in petgraph::algo::tarjan_scc(&copy_graph) {
        if scc.len() == 1
            && contained_spans
                .get(&scc[0])
                .is_none_or(|i| i.iter().all(|s| s.value != scc[0]))
        {
            continue;
        }
        let scc_set = HashSet::<TypePathElem<&str>>::from_iter(scc.iter().copied());
        use_errors.push(
            ConversionError::Cycle(
                scc.iter()
                    .map(|s| {
                        (
                            s.to_string().spanned(spans[s]),
                            contained_spans
                                .get(s)
                                .into_iter()
                                .flatten()
                                .filter(|s| scc_set.contains(&s.value))
                                .map(|s| (*s).map(|s| s.to_string()))
                                .collect(),
                        )
                    })
                    .collect(),
            )
            .spanned(spans[&scc[0]]),
        );

        node_removals.extend(scc);
    }

    for removal in node_removals {
        copy_graph.remove_node(removal);
    }

    macro_rules! meta {
        ($name:expr) => {
            ConvertMeta {
                symbols: &symbols,
                add_value: &mut add_value,
                object_name: $name,
            }
        };
    }

    match petgraph::algo::toposort(&copy_graph, None) {
        Ok(order) => {
            let order = order.into_iter().map(|o| o.to_owned()).collect::<Vec<_>>();
            for item in order {
                let val = match convert::convert_copy_value(
                    &values.copies[item.as_str()].value,
                    meta!(item.borrow()),
                ) {
                    Ok(v) => v,
                    Err(err) => {
                        use_errors.push(err);
                        continue;
                    }
                };

                symbols.uses.insert(item.to_owned(), RefCopy::Resolved(val));
            }
        }
        Err(_) => unreachable!("We removed all scc before running toposort"),
    }

    let mut ok = Vec::new();
    let mut err = use_errors;

    for (ident, binding) in values.values.iter() {
        let ref_ty = match symbols.resolve_asset(
            &Path {
                leading: Vec::new().spanned(ident.span.sub_span(0..0)),
                last: PathEnd::Ident(ident.clone()).spanned(ident.span),
            }
            .spanned(ident.span),
        ) {
            Ok((ty, _)) => ty,
            Err(e) => {
                err.push(e);
                continue;
            }
        };

        let ty = match symbols.ctx.type_registry().key_type(ref_ty).kind {
            types::TypeKind::Ref(type_id) => type_id,
            _ => unreachable!("Invariant"),
        };

        let ident = TypePathElem::new(ident.as_str()).expect("Invariant");

        match convert_object(path, &binding.value, ty, meta!(ident)) {
            Ok(obj) => ok.push(obj),
            Err(e) => err.push(e),
        }
    }

    if err.is_empty() {
        objects.extend(ok);
        Ok(objects)
    } else {
        Err(err.into())
    }
}

fn find_copy_refs<'a>(
    val: &ParseVal,
    symbols: &'a Symbols,
    found: &mut impl FnMut(Spanned<TypePathElem<&'a str>>),
) {
    for obj in val.attributes.values() {
        find_copy_refs(obj, symbols, found)
    }

    match &val.value.value {
        Value::Ref(reference) => {
            if let Some(ident) = reference.as_ident() {
                if let Some((ident, _)) = symbols.try_resolve_copy(&ident) {
                    found(ident.spanned(reference.span()))
                }
            }
        }
        Value::Map(map) => {
            for (k, v) in map.iter() {
                find_copy_refs(k, symbols, found);
                find_copy_refs(v, symbols, found);
            }
        }
        Value::Struct(FieldsKind::Named(fields)) => {
            for obj in fields.values() {
                find_copy_refs(obj, symbols, found)
            }
        }
        Value::Enum(_, inner) | Value::Transparent(inner) => find_copy_refs(inner, symbols, found),
        Value::Tuple(fields)
        | Value::Array(fields)
        | Value::Struct(FieldsKind::Unnamed(fields)) => {
            for obj in fields.iter() {
                find_copy_refs(obj, symbols, found);
            }
        }
        Value::Or(_) | Value::Primitive(_) | Value::Struct(FieldsKind::Unit) => {}
    }
}

/// Converts a parsed value to a object value. With a conversion context and existing symbols. Also does some rudementory checking if the symbols are okay.
fn convert_object<F: FnMut(TypePathElem<&str>, Val, &Symbols) -> Result<Value>>(
    path: TypePath<&str>,
    value: &ParseVal,
    expected_type: TypeId,
    mut meta: ConvertMeta<F>,
) -> Result<Object> {
    let value = value.convert(meta.reborrow(), expected_type, no_attr())?;

    create_object(path, meta.object_name, value, meta.symbols)
}

fn create_object(
    path: TypePath<&str>,
    name: TypePathElem<&str>,
    value: Val,
    symbols: &Symbols,
) -> Result<Object> {
    if symbols.ctx.type_registry().impls_top_level_type(*value.ty) {
        Ok(Object {
            object_path: path.join(&name),
            value,
        })
    } else {
        Err(ConversionError::MissingRequiredTrait {
            tr: symbols.ctx.type_registry().top_level_trait(),
            ty: *value.ty,
        }
        .spanned(value.span()))
    }
}
