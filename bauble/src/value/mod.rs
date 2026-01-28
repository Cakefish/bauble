use std::{collections::HashMap, hash::Hash};

use indexmap::IndexMap;
use rust_decimal::Decimal;

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

pub use convert::AdditionalUnspannedObjects;
pub(crate) use convert::AnyVal;
use convert::{AdditionalObjects, ConvertMeta, ConvertValue, no_attr, value_type};
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

impl ValueContainer for AnyVal<'_> {
    type ContainerField = Ident;

    fn has_attributes(&self) -> bool {
        match self {
            AnyVal::Parse(v) => v.has_attributes(),
            AnyVal::Complete(v) => v.has_attributes(),
            AnyVal::Unspanned(v) => v.has_attributes(),
        }
    }

    fn container_ty(&self) -> TypeId {
        match self {
            AnyVal::Parse(v) => v.ty(),
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

    /// Iterate the values of all attributes mutably.
    pub fn values_mut(&mut self) -> impl ExactSizeIterator<Item = &mut V> {
        self.0.values_mut()
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

    /// Get the inner fields value mutably.
    pub fn get_inner_mut(&mut self) -> &mut Fields<V> {
        &mut self.0
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
/// This is the fundamental building block of interpreteting Bauble.
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
    /// Path that refers to this object.
    pub object_path: TypePath,
    // TODO: update doc in stage 2
    /// `true` when this object appears at the top of a file and its name matches the file. The
    /// object's path will be reduced to just the path of the file.
    pub top_level: bool,
    pub value: Inner,
}

impl Object<Val> {
    #[allow(missing_docs)]
    pub fn into_unspanned(self) -> Object<UnspannedVal> {
        Object {
            object_path: self.object_path,
            top_level: self.top_level,
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
///
/// What they are referencing needs to be loaded in order to determine their type.
pub(crate) struct DelayedRegister {
    asset: Spanned<TypePath>,
    asset_kind: crate::AssetKind,
    reference: Spanned<PathKind>,
    /// The type we want a potential reference to resolve into.
    expected_ty_path: Option<Spanned<PathKind>>,
}

pub(crate) fn resolve_delayed(
    mut delayed: Vec<DelayedRegister>,
    ctx: &mut crate::context::BaubleContext,
) -> std::result::Result<(), Vec<Spanned<ConversionError>>> {
    loop {
        let mut errors = Vec::new();
        let old_len = delayed.len();

        // Try to register delayed registers, and remove them as they succeed.
        delayed.retain(|d| {
            if let Some(r) = match &d.reference.value {
                PathKind::Direct(path) => ctx.get_ref(path.borrow()),
                // TODO: what if indirect path becomes ambiguous due to later registered items that
                // were delayed?
                PathKind::Indirect(path, ident) => {
                    ctx.ref_with_ident(path.borrow(), ident.borrow())
                }
            } && let Some((ty, _, _)) = &r.asset
            {
                // TODO: for now, it is assumed all references which explicitly
                // specify their inner type should have that inner type resolved
                // by this point. If that is not the case, this should be a
                // nested reference, and in the case it is a nested reference
                // this code can optionally work or not work, depending on the
                // order the references appear in Bauble. This is unpredictable
                // and weird, it is likely best to simply error in general if it
                // is noticed that nested references are explictly being written
                // in bauble at all, and they should instead prefer having their
                // types implicitly solved.
                if let Some(desired_ty) = &d.expected_ty_path {
                    let span = desired_ty.span;
                    let path = &desired_ty.value;
                    let Some(desired_ty) = (match path {
                        PathKind::Direct(path) => ctx.get_ref(path.borrow()),
                        PathKind::Indirect(path, ident) => {
                            ctx.ref_with_ident(path.borrow(), ident.borrow())
                        }
                    }) else {
                        errors.push(
                            ConversionError::Custom(crate::CustomError::new(format!(
                                "Invalid explicit reference path '{path}'"
                            )))
                            .spanned(span),
                        );
                        return false;
                    };

                    let Some(desired_ty) = desired_ty.ty else {
                        errors.push(
                            ConversionError::Custom(crate::CustomError::new(format!(
                                "Expected path to refer to type '{path}'",
                            )))
                            .spanned(span),
                        );
                        return false;
                    };

                    if desired_ty != *ty {
                        errors.push(
                            ConversionError::ExpectedExactType {
                                expected: desired_ty,
                                got: Some(*ty),
                            }
                            .spanned(span),
                        );
                    }
                }
                if let Err(e) = ctx.register_asset(d.asset.value.borrow(), *ty, d.asset_kind) {
                    errors.push(ConversionError::Custom(e).spanned(d.asset.span))
                }
                false
            } else {
                true
            }
        });

        if !errors.is_empty() {
            return Err(errors);
        }

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

            for scc in petgraph::algo::tarjan_scc(&graph) {
                if scc.len() == 1 {
                    if map[&scc[0]].could_be(scc[0].borrow()) {
                        // Ref refers to itself
                        errors.push(
                            ConversionError::Cycle(vec![(
                                scc[0].to_string().spanned(scc[0].span),
                                vec![map[&scc[0]].to_string().spanned(map[&scc[0]].span)],
                            )])
                            .spanned(scc[0].span),
                        )
                    } else {
                        // TODO: Is this path possible? Wouldn't Ref have to refer to itself for
                        // scc.len() == 1?
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

/// Computes the path of an object.
///
/// Normally, the path is just the files's bauble path joined with the object name.
///
/// If an object is the first in the file and its name matches the file name, it receives a special
/// path that is just the file's bauble path.
fn object_path(
    file_path: TypePath<&str>,
    ident: &TypePathElem<&str>,
    binding: &crate::parse::Binding,
) -> TypePath<String> {
    if binding.is_first && {
        let file_name = file_path
            .split_end()
            .expect("file_path must not be empty")
            .1;
        *ident == file_name
    } {
        file_path.to_owned()
    } else {
        file_path.join(ident)
    }
}

pub(crate) fn register_assets(
    file_path: TypePath<&str>,
    ctx: &mut crate::context::BaubleContext,
    values: &ParseValues,
) -> std::result::Result<Vec<DelayedRegister>, Vec<Spanned<ConversionError>>> {
    let mut errors = Vec::new();
    let mut delayed = Vec::new();

    let mut symbols = Symbols::new(ctx);
    // Add `uses` to local `Symbols` instance
    for use_path in &values.uses {
        // TODO: This will error if the referenced file is yet to be passed register_assets
        if let Err(e) = symbols.add_use(use_path) {
            errors.push(e);
        }
    }

    // Move `uses` in/out of `Symbols` every loop so we have mutable access to `ctx` at certain
    // points.
    let Symbols { mut uses, .. } = symbols;

    // TODO: Register these in a correct order to allow for assets referencing assets.
    for (ident, binding) in &values.values {
        let span = ident.span;
        let ident = &TypePathElem::new(ident.as_str()).expect("Invariant");
        let path = object_path(file_path, ident, binding);
        let top_level = path.borrow() == file_path;
        let kind = if top_level {
            crate::AssetKind::TopLevel
        } else {
            crate::AssetKind::Local
        };
        let symbols = Symbols { ctx: &*ctx, uses };

        // To register an asset we need to determine its type.
        let ty = if let Some(ty) = &binding.type_path
            // If the value is a reference, then an explicit type should
            // still be delayed. The reason why it should be delayed is
            // because the type of the reference `Ref<T>`, where `T` is
            // the type of the referenced object, may not exist at this
            // point, and as such trying to resolve the type may cause
            // issues because the type is not known and depends on the
            // order the reference was created compared to the
            // referenced object, which is undesired behaviour.
            && !matches!(binding.value.value.value, Value::Ref(_))
        {
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
                && let Value::Ref(reference) = &*binding.value.value
                && let Ok(reference) = symbols.resolve_path(reference)
            {
                let expected_ty_path = if let Some(expected_ty_path) = &binding.type_path {
                    match symbols.resolve_path(expected_ty_path) {
                        Ok(s) => Some(s),
                        Err(e) => {
                            errors.push(e);
                            None
                        }
                    }
                } else {
                    None
                };

                delayed.push(DelayedRegister {
                    expected_ty_path,
                    asset_kind: kind,
                    asset: path.spanned(span),
                    reference,
                });
                Symbols { uses, .. } = symbols;
                continue;
            }

            res
        };

        Symbols { uses, .. } = symbols;
        let ref_ty = ty.and_then(|ty| {
            ctx.register_asset(path.borrow(), ty, kind)
                .map_err(|e| ConversionError::Custom(e).spanned(span))
        });
        match ref_ty {
            Ok(ref_ty) => {
                let mut symbols = Symbols { ctx: &*ctx, uses };
                // Add to Symbols::uses so other items in the same file can directly reference this
                // without full path.
                if let Err(e) = symbols.add_ref(
                    ident.to_owned(),
                    PathReference {
                        ty: None,
                        asset: Some((ref_ty, path.clone(), kind)),
                        module: None,
                    },
                ) {
                    errors.push(e.spanned(binding.value.value.span));
                }
                Symbols { uses, .. } = symbols;
            }
            Err(err) => errors.push(err),
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
    for use_path in values.uses {
        if let Err(e) = use_symbols.add_use(&use_path) {
            use_errors.push(e);
        }
    }

    let mut symbols = default_symbols.clone();

    let file_path = symbols.ctx.get_file_path(file);

    // Add asset
    for (ident, binding) in &values.values {
        let span = ident.span;
        let ident = TypePathElem::new(ident.as_str()).expect("Invariant");
        let path = object_path(file_path, &ident, binding);

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
                use_errors.push(e.spanned(span));
            }
        } else {
            // Didn't pre-register assets.
            use_errors.push(ConversionError::UnregisteredAsset.spanned(span));
        }
    }

    symbols.add(use_symbols);

    let mut additional_objects = AdditionalObjects::new(file_path.to_owned());

    let default_span = crate::Span::new(file, 0..0);

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
        let path = object_path(file_path, &ident, binding);

        let convert_meta = ConvertMeta {
            symbols: &symbols,
            additional_objects: &mut additional_objects,
            object_name: ident,
            default_span,
        };
        let top_level = path.borrow() == file_path;
        match convert_object(path, top_level, &binding.value, ty, convert_meta) {
            Ok(obj) => ok.push(obj),
            Err(e) => err.push(e),
        }
    }

    let mut objects = additional_objects.into_objects();

    if err.is_empty() {
        objects.extend(ok);
        Ok(objects)
    } else {
        Err(err.into())
    }
}

/// Converts a parsed value to a object value using a conversion context and existing symbols. Also
/// does some rudimentary checking if the symbols are okay.
fn convert_object(
    object_path: TypePath<String>,
    top_level: bool,
    value: &ParseVal,
    expected_type: TypeId,
    mut meta: ConvertMeta,
) -> Result<Object> {
    let value = value.convert(meta.reborrow(), expected_type, no_attr())?;
    create_object(object_path, top_level, value, meta.symbols)
}

fn create_object(
    object_path: TypePath<String>,
    top_level: bool,
    value: Val,
    symbols: &Symbols,
) -> Result<Object> {
    if symbols.ctx.type_registry().impls_top_level_trait(*value.ty) {
        Ok(Object {
            object_path,
            top_level,
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

/// Compare two objects and recursively compare their sub-objects (aka sub-assets)
/// while ignoring differences in the paths that refer to those sub-objects (instead
/// checking that the values in the sub-objects are indentical).
///
/// On error returns (original_val, loaded_val) for the objects that did not match. These may be a
/// pair of sub-objects rather than the top level objects.
fn compare_objects(
    original: &UnspannedVal,
    loaded: &UnspannedVal,
    orig_map: &HashMap<TypePath, UnspannedVal>,
    loaded_map: &HashMap<TypePath, (crate::Span, UnspannedVal)>,
) -> std::result::Result<(), (UnspannedVal, UnspannedVal)> {
    let inquality_err = || (original.clone(), loaded.clone());

    original
        .attributes
        .iter()
        .try_for_each(|(n, a)| match loaded.attributes.get(n) {
            Some((_, b)) => compare_objects(a, b, orig_map, loaded_map),
            None => Err(inquality_err()),
        })?;

    match (&original.value, &loaded.value) {
        (crate::Value::Ref(a), crate::Value::Ref(b)) => {
            // Compare the sub assets rather than the paths to them.
            //
            // Note, this means object comparison will pass even when the paths to sub
            // assets change.
            if a.is_subobject() {
                let a = orig_map.get(a).unwrap();
                let (_, b) = loaded_map.get(b).unwrap();
                compare_objects(a, b, orig_map, loaded_map)
            } else if a == b {
                Ok(())
            } else {
                Err(inquality_err())
            }
        }
        (crate::Value::Tuple(a), crate::Value::Tuple(b))
        | (crate::Value::Array(a), crate::Value::Array(b))
        | (
            crate::Value::Struct(crate::FieldsKind::Unnamed(a)),
            crate::Value::Struct(crate::FieldsKind::Unnamed(b)),
        ) => {
            if a.len() != b.len() {
                Err(inquality_err())
            } else {
                a.iter()
                    .zip(b.iter())
                    .try_for_each(|(a, b)| compare_objects(a, b, orig_map, loaded_map))
            }
        }
        (crate::Value::Map(a), crate::Value::Map(b)) => {
            if a.len() != b.len() {
                Err(inquality_err())
            } else {
                a.iter()
                    .zip(b.iter())
                    .try_for_each(|((k_a, v_a), (k_b, v_b))| {
                        compare_objects(k_a, k_b, orig_map, loaded_map)?;
                        compare_objects(v_a, v_b, orig_map, loaded_map)
                    })
            }
        }
        (
            crate::Value::Struct(crate::FieldsKind::Unit),
            crate::Value::Struct(crate::FieldsKind::Unit),
        ) => Ok(()),
        (
            crate::Value::Struct(crate::FieldsKind::Named(a)),
            crate::Value::Struct(crate::FieldsKind::Named(b)),
        ) => {
            if a.len() != b.len() {
                Err(inquality_err())
            } else {
                a.iter().try_for_each(|(n, a)| match b.get(n) {
                    Some(b) => compare_objects(a, b, orig_map, loaded_map),
                    None => Err(inquality_err()),
                })
            }
        }
        (crate::Value::Or(a), crate::Value::Or(b)) => {
            if a == b {
                Ok(())
            } else {
                Err(inquality_err())
            }
        }
        (crate::Value::Primitive(a), crate::Value::Primitive(b)) => {
            if a == b {
                Ok(())
            } else {
                Err(inquality_err())
            }
        }
        (crate::Value::Transparent(a), crate::Value::Transparent(b)) => {
            compare_objects(a, b, orig_map, loaded_map)
        }
        (crate::Value::Enum(n_a, a), crate::Value::Enum(n_b, b)) => {
            if n_a != n_b {
                Err(inquality_err())
            } else {
                compare_objects(a, b, orig_map, loaded_map)
            }
        }
        _ => Err(inquality_err()),
    }
}

/// Error returned by [`compare_object_sets`].
pub struct CompareObjectsError {
    /// Objects with the same path but non-equal content.
    pub mismatched: Vec<(TypePath, crate::Span, UnspannedVal, UnspannedVal)>,
    /// Objects from the original set that are missing in the new set.
    pub missing: Vec<(TypePath, UnspannedVal)>,
    /// Objects only found in the new set.
    pub new: Vec<(TypePath, UnspannedVal)>,
}

/// Compares two sets of objects and returns an error with the list of mismatched, missing, and new
/// objects if they don't match.
///
/// This is used to test that `Object`s content is preserved in a round-trip through the text format.
///
/// Ignores differences in the paths of sub-assets and only compares their content where they
/// appear in the parent objects.
pub fn compare_object_sets(
    original: impl Iterator<Item = Object<UnspannedVal>>,
    loaded: impl Iterator<Item = Object>,
) -> std::result::Result<(), CompareObjectsError> {
    let original_object_map: HashMap<_, _> =
        original.map(|obj| (obj.object_path, obj.value)).collect();
    let loaded_object_map: HashMap<_, _> = loaded
        .map(|obj| {
            (
                obj.object_path,
                (obj.value.value.span, obj.value.into_unspanned()),
            )
        })
        .collect();

    let mut missing = Vec::new();
    let mut mismatched = Vec::new();

    for (k, a) in original_object_map.iter() {
        // Don't compare sub-assets, they will be compared by recursion in `compare_objects`
        if !k.is_subobject() {
            if let Some((span, b)) = loaded_object_map.get(k) {
                if let Err((original, new)) =
                    compare_objects(a, b, &original_object_map, &loaded_object_map)
                {
                    mismatched.push((k.to_owned(), *span, original, new));
                }
            } else {
                missing.push((k.to_owned(), a.clone()));
            }
        }
    }

    let new = loaded_object_map
        .into_iter()
        // `compare_objects` handles checking for sub-asset so we don't produce
        // an error if their paths change.
        .filter(|(k, _)| !original_object_map.contains_key(k) && !k.is_subobject())
        .map(|(k, (_span, b))| (k, b))
        .collect::<Vec<_>>();

    if mismatched.is_empty() && missing.is_empty() && new.is_empty() {
        Ok(())
    } else {
        Err(CompareObjectsError {
            mismatched,
            missing,
            new,
        })
    }
}
