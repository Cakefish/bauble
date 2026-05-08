mod convert;
mod display;
mod early_context;
mod error;
mod symbols;

use std::{collections::HashMap, hash::Hash};

use indexmap::IndexMap;
use rust_decimal::Decimal;

use crate::{
    BaubleErrors, FileId, VariantKind,
    object_path::ObjectPath,
    parse::{BindingIdent, ParseVal, ParseValues, Path, PathEnd},
    path::{TypePath, TypePathElem},
    spanned::{SpanExt, Spanned},
    types::{self, TypeId, TypeRegistry},
};

pub use convert::AdditionalUnspannedObjects;
pub(crate) use convert::AnyVal;
use convert::{AdditionalObjects, ConvertMeta, ConvertValue};
pub use display::{DisplayConfig, IndentedDisplay, display_formatted};
pub(crate) use early_context::EarlyContext;
use error::Result;
pub use error::{AmbiguousWithIdent, ConversionError, RefError, RefKind};
use symbols::EarlySymbols;
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

    type Ref = ObjectPath;

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

    type Ref = ObjectPath;

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
    pub object_path: ObjectPath,
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

/// We can delay registering `Ref` assets if what they're referencing hasn't been loaded yet.
///
/// What they are referencing needs to be loaded in order to determine their type.
#[derive(Debug)]
pub(crate) struct DelayedRegister {
    path: Spanned<ObjectPath>,
    /// Full path to the referenced asset.
    reference: ObjectPath,
    /// Unresolved path to the referenced asset.
    reference_original: Spanned<Path>,
    /// The type we want a potential reference to resolve into.
    expected_ty_path: Option<Spanned<PathKind>>,
}

pub(crate) fn resolve_delayed(
    mut delayed: Vec<DelayedRegister>,
    ctx: &mut crate::context::BaubleContext,
    local_ctx: &mut crate::local_context::LocalContext,
) -> std::result::Result<(), Vec<Spanned<ConversionError>>> {
    loop {
        let mut errors = Vec::new();
        let old_len = delayed.len();

        // Try to register delayed registers, and remove them as they succeed.
        delayed.retain(|d| {
            let ty = match &d.reference {
                ObjectPath::Top(path) => ctx
                    .get_ref(path.borrow())
                    .and_then(|r| r.asset)
                    .map(|(ty, _)| ty),
                ObjectPath::Local(path) => local_ctx.get(path.borrow()),
                ObjectPath::Inline(_) => unreachable!(),
            };
            if let Some(ty) = ty {
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
                            match ctx.ref_with_ident(path.borrow(), ident.borrow()) {
                                Ok(reference) => reference,
                                Err(e) => {
                                    errors.push(e.spanned(span).into());
                                    return false;
                                }
                            }
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

                    if desired_ty != ty {
                        errors.push(
                            ConversionError::ExpectedExactType {
                                expected: desired_ty,
                                got: Some(ty),
                            }
                            .spanned(span),
                        );
                    }
                }

                match &*d.path {
                    ObjectPath::Top(path) => ctx.register_asset(path.borrow(), ty),
                    ObjectPath::Local(path) => local_ctx.register(path.clone(), ty, ctx),
                    ObjectPath::Inline(_) => {
                        unreachable!("can't be returned from object_ident_path")
                    }
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
                let node_a = graph.add_node(a.path.as_ref().map(|p| p.borrow()));
                map.insert(node_a, (&a.reference, &a.reference_original));

                for b in delayed.iter() {
                    if a.reference == *b.path {
                        graph.add_edge(node_a, b.path.as_ref().map(|p| p.borrow()), ());
                    }
                }
            }

            for scc in petgraph::algo::tarjan_scc(&graph) {
                // len == 1
                if let [referer] = scc.as_slice() {
                    let (referenced, referenced_original) = map[referer];
                    if referenced.borrow() == **referer {
                        // Ref refers to itself
                        errors.push(
                            ConversionError::Cycle(vec![(
                                referer.map(|r| format!("{r:?}")),
                                vec![referenced_original.as_ref().map(|r| format!("{r:?}"))],
                            )])
                            .spanned(referer.span),
                        )
                    } else {
                        // We make sure that the referenced asset exists in the pre-registered
                        // assets before producing `DelayedRegister`. So this error will only occur
                        // if the referenced asset's type failed to resolve (such that it wasn't
                        // registered in resolve_delayed).
                        errors.push(
                            ConversionError::Custom(crate::CustomError::new(format!(
                                "{referenced_original} refers to an asset that failed to register",
                            )))
                            .spanned(referenced_original.span),
                        );
                    }
                } else {
                    let cycle = scc
                        .iter()
                        .map(|s| {
                            (
                                format!("{s:?}").spanned(s.span),
                                vec![map[s].1.as_ref().map(|r| format!("{r:?}"))],
                            )
                        })
                        .collect();
                    errors.push(ConversionError::Cycle(cycle).spanned(scc[0].span));
                }
            }

            return Err(errors);
        }
    }
}

/// Returns the identifier and the path of an object.
///
/// The top level object in each file will have a path that matches the path of the file containing
/// it and be wrapped in `ObjectPath::Top`. The identifier for these objects is always "0" and it
/// can be referred to locally in the same file using this identifier.
///
/// For all other objects with binding are local object. For these, the path is just the file's
/// bauble path joined with the object identifier and they are wrapped in `ObjectPath::Local`.
fn object_ident_path<'a>(
    file_path: TypePath<&str>,
    binding_ident: &'a BindingIdent,
) -> (TypePathElem<&'a str>, ObjectPath) {
    let ident = TypePathElem::new(binding_ident.as_str()).expect("Invariant");
    let path = match binding_ident {
        BindingIdent::TopLevel(_) => ObjectPath::Top(file_path.to_owned()),
        BindingIdent::Local(_) => ObjectPath::Local(file_path.join(&ident)),
    };
    (ident, path)
}

/// Registers all new top level asset paths into [`EarlyContext`] so they will be known for
/// resolving full paths from `use`s in [`register_assets`].
///
/// We need to know what items brought into scope with `use` are assets rather than types or
/// modules to properly dertermine the full path (otherwise there could be multiple candidates
/// because items from different namespaces can have the same name).
pub(crate) fn pre_register_assets(
    ctx: &mut EarlyContext<'_>,
    file_path: TypePath<&str>,
    values: &ParseValues,
) {
    for ident in values.values.keys() {
        let (_ident, path) = object_ident_path(file_path, ident);

        match path {
            ObjectPath::Top(path) => ctx.register_asset(path.borrow()),
            // These don't need to be pre-registered, because we can add their full path directly
            // to Symbols, and they aren't needed to resolve `use` based paths since they can only
            // be referenced from the same file..
            ObjectPath::Local(_) => {}
            ObjectPath::Inline(_) => unreachable!("can't be returned from object_ident_path"),
        }
    }
}

pub(crate) fn register_assets(
    ctx: &mut EarlyContext<'_>,
    local_ctx: &mut crate::local_context::LocalContext,
    file_path: TypePath<&str>,
    values: &ParseValues,
) -> std::result::Result<Vec<DelayedRegister>, Vec<Spanned<ConversionError>>> {
    let mut errors = Vec::new();
    let mut delayed = Vec::new();

    let mut symbols = EarlySymbols::new(ctx, local_ctx);
    // Add `uses` to local symbols instance.
    for use_path in &values.uses {
        if let Err(e) = symbols.add_use(use_path) {
            errors.push(e);
        }
    }

    // Add assets from this file to Symbols::use.
    for ident in values.values.keys() {
        let span = ident.span();
        let (ident, path) = object_ident_path(file_path, ident);

        // Note, we don't need to lookup these in contexts because we know the full paths and that
        // the types are not known for any of them.
        let path = match path {
            ObjectPath::Top(path) => {
                debug_assert!(
                    symbols
                        .ctx
                        .get_ref(path.borrow())
                        .is_some_and(|r| r.asset.is_some_and(|(ty, p)| ty.is_none() && p == path))
                );
                path
            }
            ObjectPath::Local(path) => path,
            ObjectPath::Inline(_) => unreachable!("can't be returned from object_ident_path"),
        };
        let ty = None;

        if let Err(e) = symbols.add_local_object(ident.to_owned(), ty, path) {
            errors.push(e.spanned(span));
        }
    }

    // Resolve asset types and register the assets into `BaubleContext`.
    //
    // If the asset is a reference to another asset whose type is yet to be resolved, type
    // resolution will be delayed by pushing an entry to `delayed`. These are then handled by
    // `resolve_delayed`.
    for (ident, binding) in &values.values {
        let span = ident.span();
        let (_ident, path) = object_ident_path(file_path, ident);

        // To register an asset we need to determine its type.
        let ty = if let Some(ty) = &binding.type_path
            // If the value is a reference, resolving an explicit type to a type
            // ID should be delayed. The type of the reference `Ref<T>` is only
            // registered when registering an object of type `T`. So the when
            // the referenced object has yet to be registered, the reference
            // type may not exist. Thus, trying to resolve the type at this
            // point can fail.
            && !matches!(&*binding.value.value, Value::Ref(_))
        {
            symbols.resolve_type(ty)
        } else {
            let res = convert::value_type(&binding.value, &symbols)
                .map(|v| {
                    convert::default_value_type(
                        symbols.ctx.type_registry(),
                        binding.value.value.value.primitive_type(),
                        v,
                    )
                })
                .transpose()
                .unwrap_or(Err(
                    ConversionError::UnresolvedType.spanned(binding.value.value.span)
                ))
                .and_then(|v| {
                    if symbols.ctx.type_registry().key_type(v).kind.instanciable() {
                        Ok(v)
                    } else {
                        Err(ConversionError::UnresolvedType.spanned(binding.value.value.span))
                    }
                });

            if res.is_err()
                && let Value::Ref(ref_path) = &*binding.value.value
                // Note: If this fails, then `value_type()` would have produced the same error
                // already in `res` from calling `symbols.resolve_asset_type()` which uses
                // `resolve_path` internally. So there is no extra information from this error.
                //
                // We use `resolve_asset` instead of just `resolve_path` because the asset should
                // exist due to `pre_register_assets` or we will invevitably produce an error
                // anyway, and the errors produced in register_assets are better than
                // `resolve_delayed` because `symbols.uses` is available.
                && let Ok((maybe_ty, reference)) = symbols.resolve_asset(ref_path)
            {
                debug_assert!(
                    maybe_ty.is_none(),
                    "value_type should not produce an error if the referenced type is known"
                );
                let expected_ty_path = if let Some(expected_ty_path) = &binding.type_path {
                    // Resolving to a full path won't fail even if the reference type is not yet
                    // registered.
                    match symbols.resolve_full_path_for_type(expected_ty_path) {
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
                    path: path.spanned(span),
                    reference,
                    reference_original: ref_path.clone().spanned(binding.value.span()),
                    expected_ty_path,
                });
                continue;
            }

            if let Ok(_res) = res
                // We skipped `resolve_type` above because `Ref<T>` might not be registered, but if we
                // found referenced asset in `value_type`, then the asset is already registered so
                // `Ref<T>` will either also be registered or it will be the wrong type.
                && let Some(ty) = &binding.type_path
            {
                // TODO: Unfortunately, the error is "Expected this path to refer to a type" when
                // the `Ref<T>` isn't registered which is misleading as the actual issue is that it
                // is the wrong type for `T`. Maybe we should just register the `Ref<T>` when
                // registering each new type `T`, rather than when encountering an asset of type
                // `T`. Is there any downside to this approach?
                symbols.resolve_type(ty)
            } else {
                res
            }
        };

        let (ctx, local_ctx) = symbols.ctx_for_register();
        match ty {
            Ok(ty) => match path {
                ObjectPath::Top(path) => ctx.register_asset(path.borrow(), ty),
                ObjectPath::Local(path) => local_ctx.register(path.clone(), ty, ctx),
                ObjectPath::Inline(_) => unreachable!("can't be returned from object_ident_path"),
            },
            Err(e) => errors.push(e),
        }
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
    ctx: &crate::context::BaubleContext,
    local_ctx: &crate::local_context::LocalContext,
) -> std::result::Result<Vec<Object>, BaubleErrors> {
    let mut errors = Vec::new();

    let mut symbols = Symbols::new(ctx);
    for use_path in values.uses {
        if let Err(e) = symbols.add_use(&use_path) {
            errors.push(e);
        }
    }

    let file_path = symbols.ctx.get_file_path(file);

    // Add assets from this file to Symbols::use.
    for ident in values.values.keys() {
        let span = ident.span();
        let (ident, path) = object_ident_path(file_path, ident);

        let asset = match path {
            ObjectPath::Top(path) => symbols.ctx.get_ref(path.borrow()).and_then(|r| r.asset),
            ObjectPath::Local(path) => local_ctx.get(path.borrow()).map(|ty| (ty, path.clone())),
            ObjectPath::Inline(_) => unreachable!("can't be returned from object_ident_path"),
        };

        let Some((ty, path)) = asset else {
            // Didn't register assets.
            errors.push(ConversionError::UnregisteredAsset.spanned(span));
            continue;
        };

        if let Err(e) = symbols.add_local_object(ident.to_owned(), ty, path) {
            errors.push(e.spanned(span));
        }
    }

    let default_span = crate::Span::new(file, 0..0);
    let mut additional_objects = AdditionalObjects::new(file_path.to_owned());
    let mut objects = Vec::new();

    for (ident, binding) in &values.values {
        let ref_ty = match symbols.resolve_asset(
            &Path {
                leading: Vec::new().spanned(ident.span().sub_span(0..0)),
                last: PathEnd::Ident(ident.as_str().to_owned().spanned(ident.span()))
                    .spanned(ident.span()),
            }
            .spanned(ident.span()),
        ) {
            Ok((ty, _)) => ty,
            Err(e) => {
                errors.push(e);
                continue;
            }
        };

        let type_registry = symbols.ctx.type_registry();
        let ty = match type_registry.key_type(ref_ty).kind {
            types::TypeKind::Ref(type_id) => type_id,
            _ => unreachable!("The type registered with an object is always a reference"),
        };

        let (ident, path) = object_ident_path(file_path, ident);

        let convert_meta = ConvertMeta {
            symbols: &symbols,
            additional_objects: &mut additional_objects,
            object_name: ident,
            default_span,
        };
        match convert_object(path, &binding.value, ty, convert_meta) {
            Ok(obj) => objects.push(obj),
            Err(e) => errors.push(e),
        }
    }

    let mut all_objects = additional_objects.into_objects();

    if errors.is_empty() {
        all_objects.extend(objects);
        Ok(all_objects)
    } else {
        Err(errors.into())
    }
}

/// Converts a parsed value to a object value using a conversion context and existing symbols. Also
/// does some rudimentary checking if the symbols are okay.
fn convert_object(
    object_path: ObjectPath,
    value: &ParseVal,
    expected_type: TypeId,
    mut meta: ConvertMeta,
) -> Result<Object> {
    let value = value.convert(meta.reborrow(), expected_type, convert::no_attr())?;
    let types = meta.symbols.ctx.type_registry();
    create_object(object_path, value, types)
}

fn create_object(
    object_path: ObjectPath,
    value: Val,
    type_registry: &TypeRegistry,
) -> Result<Object> {
    if type_registry.impls_top_level_trait(*value.ty) {
        Ok(Object { object_path, value })
    } else {
        Err(ConversionError::MissingRequiredTrait {
            tr: type_registry.top_level_trait(),
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
    orig_map: &HashMap<ObjectPath, UnspannedVal>,
    loaded_map: &HashMap<ObjectPath, (crate::Span, UnspannedVal)>,
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
            // Compare the inline object rather than the paths to them.
            //
            // Note, this means object comparison will pass even when
            // the paths to inline objects change.
            if let ObjectPath::Inline(_) = a
                && let ObjectPath::Inline(_) = b
            {
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
    pub mismatched: Vec<(ObjectPath, crate::Span, UnspannedVal, UnspannedVal)>,
    /// Objects from the original set that are missing in the new set.
    pub missing: Vec<(ObjectPath, UnspannedVal)>,
    /// Objects only found in the new set.
    pub new: Vec<(ObjectPath, UnspannedVal)>,
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
        // Don't compare inline objects, they will be compared by recursion in `compare_objects`
        //
        // Note, this means unreferenced inline objects won't be considered (but those should not
        // be possible).
        if !matches!(k, ObjectPath::Inline(_)) {
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
        // `compare_objects` handles checking for inline object equality and we specifically don't
        // produce an error if their paths change.
        .filter(|(k, _)| {
            !original_object_map.contains_key(k) && !matches!(k, ObjectPath::Inline(_))
        })
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
