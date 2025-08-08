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

pub(crate) use convert::AnyVal;
use convert::{ConvertMeta, ConvertValue, no_attr, value_type};
pub use display::{DisplayConfig, IndentedDisplay, display_formatted};
use error::Result;
pub use error::{ConversionError, RefError, RefKind};
pub(crate) use symbols::Symbols;

// TODO(@docs)
#[allow(missing_docs)]
pub trait ValueTrait: Clone + std::fmt::Debug {
    type Inner: ValueContainer;
    type Ref;
    type Variant: std::borrow::Borrow<str>;
    type Field: std::fmt::Debug + Clone + Hash + Eq + std::borrow::Borrow<str>;

    fn ty(&self) -> TypeId;

    fn attributes(&self) -> &Attributes<Self::Inner>;

    fn value(&self) -> &Value<Self>;

    fn to_any(&self) -> AnyVal;
}

/// A helper trait for extracting the spans out of a Bauble value.
pub trait SpannedValue: ValueTrait {
    /// The span of the type of the value.
    fn type_span(&self) -> crate::Span;

    /// The span of the parsed Bauble value.
    fn value_span(&self) -> crate::Span;

    /// The span of the attributes to the Bauble value.
    fn attributes_span(&self) -> crate::Span;

    #[allow(missing_docs)]
    fn span(&self) -> crate::Span {
        let attributes_span = self.attributes_span();
        let value_span = self.value_span();
        if attributes_span.file() == value_span.file() {
            crate::Span::new(value_span.file(), attributes_span.start..value_span.end)
        } else {
            value_span
        }
    }
}

// TODO(@docs)
#[allow(missing_docs)]
pub trait ValueContainer: Clone + std::fmt::Debug {
    type ContainerField: std::fmt::Debug + Clone + Hash + Eq + std::borrow::Borrow<str>;

    fn has_attributes(&self) -> bool;

    fn container_ty(&self) -> TypeId;

    fn container_to_any(&self) -> AnyVal;
}

impl<V: ValueTrait> ValueContainer for V {
    type ContainerField = V::Field;

    fn has_attributes(&self) -> bool {
        !self.attributes().is_empty()
    }

    fn container_ty(&self) -> TypeId {
        ValueTrait::ty(self)
    }

    fn container_to_any(&self) -> AnyVal {
        self.to_any()
    }
}

impl ValueContainer for CopyVal {
    type ContainerField = Ident;

    fn has_attributes(&self) -> bool {
        match self {
            CopyVal::Copy(v) => v.has_attributes(),
            CopyVal::Resolved(v) => v.has_attributes(),
        }
    }

    fn container_ty(&self) -> TypeId {
        match self {
            CopyVal::Copy(v) => v.ty(),
            CopyVal::Resolved(v) => v.ty(),
        }
    }

    fn container_to_any(&self) -> AnyVal {
        match self {
            CopyVal::Copy(v) => v.to_any(),
            CopyVal::Resolved(v) => v.to_any(),
        }
    }
}

impl ValueContainer for AnyVal<'_> {
    type ContainerField = Ident;

    fn has_attributes(&self) -> bool {
        match self {
            AnyVal::Parse(v) => v.has_attributes(),
            AnyVal::Copy(v) => v.has_attributes(),
            AnyVal::Complete(v) => v.has_attributes(),
            AnyVal::Unspanned(v) => v.has_attributes(),
        }
    }

    fn container_ty(&self) -> TypeId {
        match self {
            AnyVal::Parse(v) => v.ty(),
            AnyVal::Copy(v) => v.ty(),
            AnyVal::Complete(v) => v.ty(),
            AnyVal::Unspanned(v) => v.ty(),
        }
    }

    fn container_to_any(&self) -> AnyVal {
        *self
    }
}

/// A map of Bauble attributes.
#[derive(Clone, Debug, PartialEq)]
pub struct Attributes<V: ValueContainer = Val>(Fields<V>);

impl<V: ValueContainer> From<Fields<V>> for Attributes<V> {
    fn from(value: IndexMap<V::ContainerField, V>) -> Self {
        Self(value)
    }
}

impl<V: ValueContainer> Default for Attributes<V> {
    fn default() -> Self {
        Self(Default::default())
    }
}

impl<V: ValueContainer> Attributes<V> {
    #[allow(missing_docs)]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    #[allow(missing_docs)]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Get the key and value of the attribute `s`.
    pub fn get(&self, s: &str) -> Option<(&V::ContainerField, &V)> {
        self.0.get_key_value(s)
    }

    /// Iterate the values of all attributes.
    pub fn values(&self) -> impl ExactSizeIterator<Item = &V> {
        self.0.values()
    }

    /// Iterate the key and value of all attributes and their fields.
    pub fn iter(&self) -> impl ExactSizeIterator<Item = (&V::ContainerField, &V)> {
        self.0.iter()
    }

    /// Get the first attribute key and value.
    pub fn first(&self) -> Option<(&V::ContainerField, &V)> {
        self.0.first()
    }

    /// Inserts an attribute `ident` with a value `v`.
    pub fn insert(&mut self, ident: V::ContainerField, v: V) {
        self.0.insert(ident, v);
    }

    /// Remove and return the value of the attribute `ident` if such an attribute exists.
    pub fn take(&mut self, ident: &str) -> Option<V> {
        self.0.swap_remove(ident)
    }

    /// Get the inner fields of an attribute.
    pub fn get_inner(&self) -> &Fields<V> {
        &self.0
    }
}

impl<T: ValueContainer> IntoIterator for Attributes<T> {
    type Item = (T::ContainerField, T);

    type IntoIter = <IndexMap<T::ContainerField, T> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a, T: ValueContainer> IntoIterator for &'a Attributes<T> {
    type Item = (&'a T::ContainerField, &'a T);

    type IntoIter = indexmap::map::Iter<'a, T::ContainerField, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

#[derive(Clone, Debug, PartialEq)]
/// A [`Value`] with type information and attributes.
pub struct Val {
    /// The type of the parsed Bauble value.
    pub ty: Spanned<TypeId>,
    /// The parsed Bauble value.
    pub value: Spanned<Value>,
    /// Attributes associated with the parsed Bauble value.
    pub attributes: Spanned<Attributes>,
}

impl ValueTrait for Val {
    type Inner = Self;

    type Ref = TypePath;

    type Variant = Spanned<TypePathElem>;

    type Field = Ident;

    fn ty(&self) -> TypeId {
        self.ty.value
    }

    fn attributes(&self) -> &Attributes<Self::Inner> {
        &self.attributes
    }

    fn value(&self) -> &Value<Self> {
        &self.value
    }

    fn to_any(&self) -> AnyVal {
        AnyVal::Complete(self)
    }
}

impl SpannedValue for Val {
    fn type_span(&self) -> crate::Span {
        self.ty.span
    }

    fn value_span(&self) -> crate::Span {
        self.value.span
    }

    fn attributes_span(&self) -> crate::Span {
        self.attributes.span
    }
}

impl Val {
    /// Return a version of `self` without span.
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

/// A [`Val`] without span information.
#[derive(Clone, Debug, PartialEq)]
pub struct UnspannedVal {
    /// The type of the parsed Bauble value.
    pub ty: TypeId,
    /// The parsed Bauble value.
    pub value: Value<UnspannedVal>,
    /// Attributes associated with the parsed Bauble value.
    pub attributes: Attributes<UnspannedVal>,
}

impl ValueTrait for UnspannedVal {
    type Inner = Self;

    type Ref = TypePath;

    type Variant = TypePathElem;

    type Field = String;

    fn ty(&self) -> TypeId {
        self.ty
    }

    fn attributes(&self) -> &Attributes<Self::Inner> {
        &self.attributes
    }

    fn value(&self) -> &Value<Self> {
        &self.value
    }

    fn to_any(&self) -> AnyVal {
        AnyVal::Unspanned(self)
    }
}

impl UnspannedVal {
    /// Create a new unspanned val.
    ///
    /// In contexts where you have a `TypeRegistry`, for example in `Bauble::construct_type`,
    /// prefer using `TypeRegistry::instantiate` to construct this for types for which
    /// `TypeId` is known.
    pub fn new(value: Value<UnspannedVal>) -> Self {
        Self {
            ty: types::TypeRegistry::any_type(),
            value,
            attributes: Attributes::default(),
        }
    }

    #[allow(missing_docs)]
    pub fn with_type(mut self, ty: TypeId) -> Self {
        self.ty = ty;
        self
    }

    #[allow(missing_docs)]
    pub fn with_attribute(mut self, ty: TypeId) -> Self {
        self.ty = ty;
        self
    }

    /// Convert this unspanned value into a spanned value by using a specfic span for all spans.
    pub fn into_spanned(self, span: crate::Span) -> Val {
        Val {
            ty: self.ty.spanned(span),
            value: match self.value {
                Value::Ref(r) => Value::Ref(r),
                Value::Tuple(seq) => {
                    Value::Tuple(seq.into_iter().map(|v| v.into_spanned(span)).collect())
                }
                Value::Array(seq) => {
                    Value::Array(seq.into_iter().map(|v| v.into_spanned(span)).collect())
                }
                Value::Map(map) => Value::Map(
                    map.into_iter()
                        .map(|(k, v)| (k.into_spanned(span), v.into_spanned(span)))
                        .collect(),
                ),
                Value::Struct(fields) => Value::Struct(match fields {
                    FieldsKind::Unit => FieldsKind::Unit,
                    FieldsKind::Unnamed(fields) => FieldsKind::Unnamed(
                        fields.into_iter().map(|v| v.into_spanned(span)).collect(),
                    ),
                    FieldsKind::Named(fields) => FieldsKind::Named(
                        fields
                            .into_iter()
                            .map(|(f, v)| (f.spanned(span), v.into_spanned(span)))
                            .collect(),
                    ),
                }),
                Value::Or(items) => Value::Or(items.into_iter().map(|v| v.spanned(span)).collect()),
                Value::Primitive(prim) => Value::Primitive(prim),
                Value::Transparent(inner) => Value::Transparent(Box::new(inner.into_spanned(span))),
                Value::Enum(variant, inner) => {
                    Value::Enum(variant.spanned(span), Box::new(inner.into_spanned(span)))
                }
            }
            .spanned(span),
            attributes: Attributes(
                self.attributes
                    .0
                    .into_iter()
                    .map(|(s, v)| (s.spanned(span), v.into_spanned(span)))
                    .collect(),
            )
            .spanned(span),
        }
    }
}

#[derive(Clone, Debug)]
pub struct CopyValInner {
    ty: Option<Spanned<TypeId>>,
    value: Spanned<Value<CopyValInner>>,
    attributes: Spanned<Attributes<CopyVal>>,
}

impl ValueTrait for CopyValInner {
    type Inner = CopyVal;

    type Ref = TypePath;

    type Variant = Spanned<TypePathElem>;

    type Field = Ident;

    fn ty(&self) -> TypeId {
        *self
            .ty
            .as_deref()
            .unwrap_or(&types::TypeRegistry::any_type())
    }

    fn attributes(&self) -> &Attributes<Self::Inner> {
        &self.attributes
    }

    fn value(&self) -> &Value<Self> {
        &self.value
    }

    fn to_any(&self) -> AnyVal {
        AnyVal::Copy(self)
    }
}

impl SpannedValue for CopyValInner {
    fn type_span(&self) -> crate::Span {
        self.ty.map(|s| s.span).unwrap_or(self.value.span)
    }

    fn value_span(&self) -> crate::Span {
        self.value.span
    }

    fn attributes_span(&self) -> crate::Span {
        self.attributes.span
    }
}

#[derive(Clone, Debug)]
pub enum CopyVal {
    Copy(CopyValInner),
    Resolved(Val),
}

impl CopyVal {
    fn span(&self) -> crate::Span {
        match self {
            CopyVal::Copy(val) => val.span(),
            CopyVal::Resolved(val) => val.span(),
        }
    }
}

pub type Ident = Spanned<String>;

#[allow(missing_docs)]
pub type Map<Inner = Val> = Vec<(Inner, Inner)>;

#[allow(missing_docs)]
pub type Fields<Inner = Val> = IndexMap<<Inner as ValueContainer>::ContainerField, Inner>;

#[allow(missing_docs)]
pub type Sequence<Inner = Val> = Vec<Inner>;

/// The kind of a field inside of Bauble.
// TODO(@docs)
#[allow(missing_docs)]
#[derive(Clone, Debug, PartialEq)]
pub enum FieldsKind<Inner: ValueContainer = Val> {
    Unit,
    Unnamed(Sequence<Inner>),
    Named(Fields<Inner>),
}

impl FieldsKind {
    #[allow(missing_docs)]
    pub fn variant_kind(&self) -> VariantKind {
        match self {
            FieldsKind::Unit => VariantKind::Path,
            FieldsKind::Unnamed(_) => VariantKind::Tuple,
            FieldsKind::Named(_) => VariantKind::Struct,
        }
    }
}

/// A value of a primitive type inside of Bauble.
#[allow(missing_docs)]
#[derive(Clone, Debug, PartialEq)]
pub enum PrimitiveValue {
    Num(Decimal),
    Str(String),
    Bool(bool),
    Unit,
    Default,
    Raw(String),
}

/// A parsed but untyped value from Bauble.
///
/// This is the fundemtnal building block of interpreteting Bauble.
/// For a typed version with attributes, see [`Val`].
#[allow(missing_docs)]
#[derive(Clone, Debug, PartialEq)]
pub enum Value<V: ValueTrait = Val> {
    // Fully resolved path.
    Ref(V::Ref),

    Tuple(Sequence<V::Inner>),
    Array(Sequence<V::Inner>),
    Map(Map<V::Inner>),

    /// Either struct or enum variant
    Struct(FieldsKind<V::Inner>),

    Or(Vec<V::Variant>),

    Primitive(PrimitiveValue),

    Transparent(Box<V::Inner>),

    Enum(V::Variant, Box<V::Inner>),
}

impl<V: ValueTrait> Default for Value<V> {
    fn default() -> Self {
        Value::Primitive(PrimitiveValue::Unit)
    }
}

impl<T: ValueTrait> Value<T> {
    /// If the value can be described by a primitive type.
    pub fn primitive_type(&self) -> Option<types::Primitive> {
        match self {
            Self::Primitive(p) => Some(match p {
                PrimitiveValue::Num(_) => types::Primitive::Num,
                PrimitiveValue::Str(_) => types::Primitive::Str,
                PrimitiveValue::Bool(_) => types::Primitive::Bool,
                PrimitiveValue::Unit => types::Primitive::Unit,
                PrimitiveValue::Raw(_) => types::Primitive::Raw,
                PrimitiveValue::Default => return None,
            }),
            _ => None,
        }
    }
}

/// Represents a value tied to a specific path.
#[allow(missing_docs)]
#[derive(Debug, Clone, PartialEq)]
pub struct Object<Inner = Val> {
    pub object_path: TypePath,
    pub value: Inner,
}

impl Object<Val> {
    #[allow(missing_docs)]
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

    let default_span = crate::Span::new(file, 0..0);

    macro_rules! meta {
        ($name:expr) => {
            ConvertMeta {
                symbols: &symbols,
                add_value: &mut add_value,
                object_name: $name,
                default_span,
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
