use std::{
    borrow::Cow,
    collections::{HashMap, HashSet},
    fmt::Display,
};

use indexmap::IndexMap;
use rust_decimal::Decimal;

use crate::{
    BaubleError, BaubleErrors, VariantKind,
    error::Level,
    parse::{self, Object as ParseObject, Path, PathEnd, PathTreeEnd, Use, Values},
    spanned::{SpanExt, Spanned},
};

mod asset_context;

pub use asset_context::*;

#[derive(Clone, Debug, Default)]
pub struct Attributes(pub IndexMap<Spanned<String>, Val>);

#[derive(Clone, Debug)]
/// A value with attributes
pub struct Val {
    pub value: Spanned<Value>,
    pub attributes: Spanned<Attributes>,
}

impl Val {
    pub fn span(&self) -> crate::Span {
        crate::Span::new(
            self.value.span.clone(),
            self.attributes.span.start..self.value.span.end,
        )
    }
}

pub type Ident = Spanned<String>;

pub type Map = Vec<(Val, Val)>;

pub type Fields = IndexMap<Ident, Val>;

pub type Sequence = Vec<Val>;

// type path.
type TypePath = Spanned<OwnedTypeInfo>;

type AssetPath = String;

#[derive(Clone, Debug)]
pub enum FieldsKind {
    Unit,
    Tuple(Sequence),
    Struct(Fields),
}

impl FieldsKind {
    pub fn variant_kind(&self) -> VariantKind {
        match self {
            FieldsKind::Unit => VariantKind::Path,
            FieldsKind::Tuple(_) => VariantKind::Tuple,
            FieldsKind::Struct(_) => VariantKind::Struct,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ValueKind {
    Unit,
    Num,
    Bool,
    Str,
    Opt,
    Ref,
    Array,
    Map,
    Tuple,
    Struct,
    Enum,
    BitFlags,
    Raw,
}

impl Display for ValueKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use ValueKind::*;

        match self {
            Unit => write!(f, "unit"),
            Num => write!(f, "number"),
            Bool => write!(f, "boolean"),
            Str => write!(f, "string"),
            Opt => write!(f, "option"),
            Ref => write!(f, "reference"),
            Array => write!(f, "array"),
            Map => write!(f, "map"),
            Tuple => write!(f, "tuple"),
            Struct => write!(f, "struct"),
            Enum => write!(f, "enum"),
            BitFlags => write!(f, "bitflags"),
            Raw => write!(f, "raw"),
        }
    }
}

#[derive(Clone, Debug)]
pub enum Value {
    Unit,
    Num(Decimal),
    Bool(bool),
    Str(String),
    Opt(Option<Box<Val>>),
    // Fully resolved path.
    Ref(AssetPath),

    Array(Sequence),
    Map(Map),

    Tuple(Option<TypePath>, Sequence),
    Struct(Option<TypePath>, FieldsKind),
    Enum(TypePath, Ident, FieldsKind),

    BitFlags(Option<TypePath>, Vec<Ident>),

    Raw(String),
}

impl Value {
    pub fn is_always_ref(&self) -> bool {
        let type_info = match self {
            Value::Tuple(Some(type_info), _)
            | Value::Struct(Some(type_info), _)
            | Value::Enum(type_info, _, _) => type_info,
            _ => return false,
        };

        type_info.is_always_ref()
    }
    pub fn attributes(&self) -> &[String] {
        let type_info = match self {
            Value::Tuple(Some(type_info), _)
            | Value::Struct(Some(type_info), _)
            | Value::Enum(type_info, _, _) => type_info,
            _ => return &[],
        };

        match &type_info.value {
            OwnedTypeInfo::Path { attributes, .. } => attributes,
            _ => &[],
        }
    }
    pub fn kind(&self) -> ValueKind {
        match self {
            Value::Unit => ValueKind::Unit,
            Value::Num(_) => ValueKind::Num,
            Value::Bool(_) => ValueKind::Bool,
            Value::Str(_) => ValueKind::Str,
            Value::Ref(_) => ValueKind::Ref,
            Value::Map(_) => ValueKind::Map,
            Value::Struct { .. } => ValueKind::Struct,
            Value::Tuple { .. } => ValueKind::Tuple,
            Value::Array(_) => ValueKind::Array,
            Value::BitFlags(_, _) => ValueKind::BitFlags,
            Value::Raw(_) => ValueKind::Raw,
            Value::Opt(_) => ValueKind::Opt,
            Value::Enum(_, _, _) => ValueKind::Enum,
        }
    }

    pub fn type_info(&self) -> OwnedTypeInfo {
        match self {
            Self::Struct(Some(type_info), _)
            | Self::BitFlags(Some(type_info), _)
            | Self::Enum(type_info, _, _) => type_info.value.clone(),
            value => OwnedTypeInfo::Kind(value.kind()),
        }
    }

    pub fn type_path(&self) -> Option<TypePath> {
        match self {
            Self::Struct(Some(type_info), _)
            | Self::BitFlags(Some(type_info), _)
            | Self::Enum(type_info, _, _) => Some(type_info.clone()),
            _ => None,
        }
    }
}

#[derive(Debug)]
pub struct Object {
    pub object_path: AssetPath,
    /// Optionally explicit type path, otherwise derive from value.
    pub type_path: Option<TypePath>,
    pub path: String,
    pub value: Val,
}

impl Object {
    pub fn value_type(&self) -> OwnedTypeInfo {
        self.type_path
            .as_ref()
            .map(|t| t.value.clone())
            .unwrap_or_else(|| self.value.value.type_info())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ConversionError {
    ModuleNotFound,
    AmbiguousUse,
    ExpectedUnit,
    ExpectedTupleFields,
    ExpectedFields,
    ExpectedBitfield,
    UnexpectedIdent,
    TooManyArguments,
    ExpectedAsset,
    ExpectedType,
    ExpectedExactType(OwnedTypeInfo),
    CopyCycle(Vec<(Spanned<String>, Vec<Spanned<String>>)>),
}

impl BaubleError for Spanned<ConversionError> {
    fn msg_general(&self) -> crate::error::ErrorMsg {
        let msg = match &self.value {
            ConversionError::CopyCycle(_) => "A copy cycle was found",
            _ => "Conversion error",
        };

        Cow::Borrowed(msg).spanned(self.span())
    }

    fn msgs_specific(&self) -> Vec<(crate::error::ErrorMsg, crate::error::Level)> {
        // TODO: Include more info in these errors.
        let msg = match &self.value {
            ConversionError::ModuleNotFound => "Module not found",
            ConversionError::AmbiguousUse => "Ambiguous use",
            ConversionError::ExpectedUnit => "Expected unit",
            ConversionError::ExpectedTupleFields => "Expected unnamed fields",
            ConversionError::ExpectedFields => "Expected named fields",
            ConversionError::ExpectedBitfield => "Expected bitfield",
            ConversionError::UnexpectedIdent => "Unexpected identifier",
            ConversionError::TooManyArguments => "Too many arguments",
            ConversionError::ExpectedAsset => "Expected asset reference",
            ConversionError::ExpectedType => "Expected a type",
            ConversionError::ExpectedExactType(type_info) => {
                return vec![(
                    Cow::<str>::Owned(format!("Expected the type `{type_info}`"))
                        .spanned(self.span()),
                    Level::Error,
                )];
            }
            ConversionError::CopyCycle(cycle) => {
                return cycle
                    .iter()
                    .flat_map(|(a, contained)| {
                        std::iter::once((
                            Cow::<str>::Owned(format!("`{a}` which depends on")).spanned(a.span()),
                            Level::Error,
                        ))
                        .chain(contained.iter().map(|b| {
                            (
                                Cow::<str>::Owned(format!("`${b}` here")).spanned(b.span()),
                                Level::Error,
                            )
                        }))
                    })
                    .collect();
            }
        };

        vec![(Cow::Borrowed(msg).spanned(self.span()), Level::Error)]
    }
}

type Result<T> = std::result::Result<T, Spanned<ConversionError>>;

#[derive(Clone)]
enum RefCopy {
    Unresolved,
    Resolved(Val),
    Ref(Reference),
}

impl Default for RefCopy {
    fn default() -> Self {
        Self::Ref(Default::default())
    }
}

impl RefCopy {
    /// # Panics
    /// Panics if self isn't a reference.
    fn unwrap_ref(&self) -> &Reference {
        match self {
            RefCopy::Ref(r) => r,
            RefCopy::Unresolved | RefCopy::Resolved(_) => panic!("Not a reference"),
        }
    }

    fn add(self, other: Reference) -> std::result::Result<Self, ConversionError> {
        match self {
            RefCopy::Unresolved | RefCopy::Resolved(_) => Err(ConversionError::AmbiguousUse),
            RefCopy::Ref(reference) => Ok(RefCopy::Ref(
                reference
                    .combined(other)
                    .ok_or(ConversionError::AmbiguousUse)?,
            )),
        }
    }
}

#[derive(Default, Clone)]
pub struct Symbols<C: AssetContext> {
    ctx: C,
    uses: HashMap<String, RefCopy>,
}

impl<C: AssetContext> Symbols<C> {
    pub fn new(ctx: C) -> Self {
        Self {
            ctx,
            uses: HashMap::default(),
        }
    }
    fn add_ref(
        &mut self,
        ident: String,
        reference: Reference,
    ) -> std::result::Result<(), ConversionError> {
        let r = self.uses.entry(ident).or_default();

        *r = r.clone().add(reference)?;

        Ok(())
    }

    fn add<U: AssetContext>(&mut self, symbols: Symbols<U>) {
        self.uses.extend(symbols.uses)
    }

    fn add_use(&mut self, use_: &Use) -> Result<()> {
        fn add_use_inner<C: AssetContext>(
            this: &mut Symbols<C>,
            leading: String,
            end: &Spanned<PathTreeEnd>,
        ) -> Result<()> {
            match &end.value {
                PathTreeEnd::Group(g) => {
                    for node in g {
                        let mut leading = leading.clone();
                        for s in &node.leading.value {
                            leading.push_str(&s.value);
                            leading.push_str("::");
                        }
                        add_use_inner(this, leading, &node.end)?;
                    }
                }
                PathTreeEnd::Everything => {
                    if let Some(uses) = this.ctx.all_in(&leading) {
                        for (ident, reference) in uses {
                            this.add_ref(ident, reference)
                                .map_err(|e| e.spanned(end.span().clone()))?;
                        }
                    } else {
                        return Err(ConversionError::ModuleNotFound.spanned(end.span()));
                    }
                }
                PathTreeEnd::PathEnd(PathEnd::Ident(ident)) => {
                    let path = format!("{leading}{ident}");
                    if let Some(reference) = this.ctx.get_ref(&path) {
                        this.add_ref(ident.value.clone(), reference)
                            .map_err(|e| e.spanned(ident.span()))?;
                    } else {
                        return Err(ConversionError::ModuleNotFound.spanned(end.span()));
                    }
                }
                PathTreeEnd::PathEnd(PathEnd::WithIdent(ident)) => {
                    if let Some(reference) = this
                        .ctx
                        .with_ident(leading.trim_end_matches(':'), ident.as_str())
                    {
                        this.add_ref(ident.value.clone(), reference)
                            .map_err(|e| e.spanned(ident.span()))?;
                    } else {
                        return Err(ConversionError::ModuleNotFound.spanned(end.span()));
                    }
                }
            }
            Ok(())
        }

        let mut leading = String::new();
        for l in use_.leading.iter() {
            leading.push_str(l);
            leading.push_str("::");
        }
        add_use_inner(self, leading, &use_.end)
    }

    fn try_resolve_copy<'a>(&'a self, ident: &str) -> Option<(&'a str, Option<Val>)> {
        let (key, value) = self.uses.get_key_value(ident)?;
        match value {
            RefCopy::Unresolved => Some((key, None)),
            RefCopy::Resolved(val) => Some((key, Some(val.clone()))),
            RefCopy::Ref(_) => None,
        }
    }

    fn get_module(&self, ident: &str) -> Option<Cow<str>> {
        self.uses
            .get(ident)
            .and_then(|reference| reference.unwrap_ref().get_module())
    }

    fn resolve_item(&self, path: &Path) -> Result<Cow<Reference>> {
        if path.leading.is_empty() {
            match &path.last.value {
                PathEnd::Ident(ident) => {
                    if let Some(asset) = self.uses.get(ident.as_str()) {
                        Ok(Cow::Borrowed(asset.unwrap_ref()))
                    } else {
                        self.ctx
                            .with_ident("", ident.as_str())
                            .ok_or(ConversionError::UnexpectedIdent.spanned(path.last.span()))
                            .map(Cow::Owned)
                    }
                }
                PathEnd::WithIdent(ident) => self
                    .ctx
                    .with_ident("", ident.as_str())
                    .ok_or(ConversionError::UnexpectedIdent.spanned(path.last.span()))
                    .map(Cow::Owned),
            }
        } else {
            let first = path.leading.first().expect("We know the Vec isn't empty.");
            let mut p = self
                .get_module(first.as_str())
                .unwrap_or(Cow::Borrowed(first.as_str()))
                .into_owned();

            for ident in &path.leading[1..] {
                p.push_str("::");
                p.push_str(ident.as_str());
            }

            match &path.last.value {
                PathEnd::WithIdent(ident) => self
                    .ctx
                    .with_ident(&p, ident.as_str())
                    .ok_or(ConversionError::UnexpectedIdent.spanned(path.last.span())),
                PathEnd::Ident(ident) => {
                    p.push_str("::");
                    p.push_str(ident.as_str());
                    self.ctx
                        .get_ref(&p)
                        .ok_or(ConversionError::UnexpectedIdent.spanned(path.last.span()))
                }
            }
            .map(Cow::Owned)
        }
    }

    fn resolve_asset(&self, path: &Spanned<Path>) -> Result<String> {
        let item = self.resolve_item(path)?;

        item.into_owned()
            .to_asset()
            .ok_or(ConversionError::ExpectedAsset.spanned(path.span()))
    }

    fn resolve_type(&self, path: &Spanned<Path>) -> Result<(TypeKind, TypePath)> {
        let item = self.resolve_item(path)?;

        item.into_owned()
            .to_type()
            .map(|kind| {
                let path = kind.type_info().spanned(path.span());
                (kind, path)
            })
            .ok_or(ConversionError::ExpectedType.spanned(path.span()))
    }

    fn resolve_bitfield(&self, path: &Spanned<Path>) -> Result<Spanned<BitField>> {
        let item = self.resolve_type(path)?;

        if let TypeKind::BitField(bitfield) = item.0 {
            Ok(bitfield.spanned(item.1.span))
        } else {
            Err(ConversionError::ExpectedBitfield.spanned(path.span()))
        }
    }
}

pub fn convert_values<C: AssetContext>(
    path: &str,
    values: Values,
    default_symbols: &Symbols<C>,
) -> std::result::Result<Vec<Object>, BaubleErrors<'static>> {
    let mut use_symbols = Symbols::new(&default_symbols.ctx);
    let mut use_errors = Vec::new();
    for use_ in values.uses {
        if let Err(e) = use_symbols.add_use(&use_) {
            use_errors.push(e);
        }
    }

    let mut symbols = default_symbols.clone();

    for (symbol, _) in &values.values {
        let path = format!("{path}::{symbol}");
        if let Err(e) = symbols
            .add_ref(
                symbol.value.clone(),
                Reference::Specific {
                    ty: None,
                    asset: Some(path),
                    module: None,
                },
            )
            .map_err(|e| e.spanned(symbol.span()))
        {
            use_errors.push(e);
        }
    }
    symbols.add(use_symbols);

    for (symbol, _) in &values.copies {
        symbols
            .uses
            .insert(symbol.value.clone(), RefCopy::Unresolved);
    }

    let mut objects = Vec::new();
    let mut name_allocs = HashMap::new();
    let mut add_value = |name: &str, mut val: Val| {
        let idx = *name_allocs
            .entry(name.to_string())
            .and_modify(|i| *i += 1u64)
            .or_insert(0);
        let name = format!("{name}@{idx}");
        let span = val.value.span();

        let mut kept_attrs = Attributes::default().spanned(span.clone());

        for attr in val.value.attributes() {
            if let Some(val) = val.attributes.0.shift_remove(attr.as_str()) {
                kept_attrs.0.insert(attr.clone().spanned(span.clone()), val);
            }
        }

        let attributes = std::mem::replace(&mut val.attributes, kept_attrs);

        objects.push(create_object(path, &name, val));
        Val {
            value: Value::Ref(format!("{path}::{name}")).spanned(span),
            attributes,
        }
    };

    let mut spans = HashMap::new();
    let mut contained_spans = HashMap::<&str, Vec<Spanned<&str>>>::new();
    let mut copy_graph = petgraph::graphmap::DiGraphMap::new();

    for (symbol, value) in &values.copies {
        spans.insert(symbol.as_str(), symbol.span());
        copy_graph.add_node(symbol.as_str());
        find_copy_refs(value, &symbols, &mut |s| {
            copy_graph.add_edge(symbol.as_str(), s.value, ());
            contained_spans.entry(symbol).or_default().push(s);
        });
    }

    let mut node_removals = Vec::new();
    for scc in petgraph::algo::tarjan_scc(&copy_graph) {
        if scc.len() == 1
            && contained_spans
                .get(scc[0])
                .is_none_or(|i| i.iter().all(|s| s.value != scc[0]))
        {
            continue;
        }
        let scc_set = HashSet::<&str>::from_iter(scc.iter().copied());
        use_errors.push(
            ConversionError::CopyCycle(
                scc.iter()
                    .map(|s| {
                        (
                            s.to_string().spanned(spans[s].clone()),
                            contained_spans
                                .get(s)
                                .into_iter()
                                .flatten()
                                .filter(|s| scc_set.contains(s.value))
                                .map(|s| s.clone().map(|s| s.to_string()))
                                .collect(),
                        )
                    })
                    .collect(),
            )
            .spanned(spans[scc[0]].clone()),
        );

        node_removals.extend(scc);
    }

    for removal in node_removals {
        copy_graph.remove_node(removal);
    }

    match petgraph::algo::toposort(&copy_graph, None) {
        Ok(order) => {
            let order = order.into_iter().map(|s| s.to_string()).collect::<Vec<_>>();

            for item in order {
                let val = match convert_value(
                    &values.copies[item.as_str()],
                    &symbols,
                    &mut add_value,
                    false,
                    &item,
                ) {
                    Ok(v) => v,
                    Err(err) => {
                        use_errors.push(err);
                        continue;
                    }
                };

                symbols.uses.insert(item, RefCopy::Resolved(val));
            }
        }
        Err(_) => unreachable!("We removed all scc before running toposort"),
    }

    let mut ok = Vec::new();
    let mut err = use_errors;

    for value in values.values.iter().map(|value| {
        convert_object(
            path,
            &value.0.value,
            &value.1.object,
            &symbols,
            &mut add_value,
        )
        .and_then(|mut object| {
            if let Some(type_path) = &value.1.type_path {
                object.type_path = Some(symbols.resolve_type(type_path)?.1);
            }
            Ok(object)
        })
    }) {
        match value {
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

fn find_copy_refs<'a, C: AssetContext>(
    object: &ParseObject,
    symbols: &'a Symbols<C>,
    found: &mut impl FnMut(Spanned<&'a str>),
) {
    for obj in object.attributes.0.values() {
        find_copy_refs(obj, symbols, found)
    }

    match &object.value.value {
        parse::Value::Ref(reference) => {
            if let Some(ident) = reference.as_ident() {
                if let Some((ident, _)) = symbols.try_resolve_copy(ident) {
                    found(ident.spanned(reference.span()))
                }
            }
        }
        parse::Value::Map(map) => {
            for (k, v) in map.iter() {
                find_copy_refs(k, symbols, found);
                find_copy_refs(v, symbols, found);
            }
        }
        parse::Value::Struct { fields, .. } => {
            for obj in fields.values() {
                find_copy_refs(obj, symbols, found)
            }
        }
        parse::Value::Tuple { fields, .. } | parse::Value::Array(fields) => {
            for obj in fields.iter() {
                find_copy_refs(obj, symbols, found);
            }
        }
        _ => {}
    }
}

fn convert_value<C: AssetContext>(
    value: &ParseObject,
    symbols: &Symbols<C>,
    add_value: &mut impl FnMut(&str, Val) -> Val,
    is_root: bool,
    object_name: &str,
) -> Result<Val> {
    let attr_name = format!("{object_name}@attr");
    let attributes = Attributes(
        value
            .attributes
            .0
            .iter()
            .map(|(ident, value)| {
                Ok((
                    ident.clone(),
                    convert_value(value, symbols, add_value, false, &attr_name)?,
                ))
            })
            .try_collect()?,
    );

    let (add_new_value, object_name) = if !is_root
        && let Some(type_path) = value.value.type_path()
        && let Ok((_, type_path)) = symbols.resolve_type(type_path)
        && type_path.is_always_ref()
        && let Some(type_path) = type_path.path()
    {
        (
            true,
            // NOTE: We do this to try and have the same type for a certain temp value ident. And we don't
            // want `::` in an ident.
            // TODO: @perf when we have type ids, use that here to differentiate and get shorter strings.
            &*format!("{object_name}@{}", type_path.to_string().replace("::", ":")),
        )
    } else {
        (false, object_name)
    };

    let val = match &value.value.value {
        parse::Value::Num(num) => Value::Num(*num),
        parse::Value::Bool(b) => Value::Bool(*b),
        parse::Value::Str(s) => Value::Str(s.clone()),
        parse::Value::Ref(path) => {
            if let Some((_, val)) = path
                .as_ident()
                .and_then(|ident| symbols.try_resolve_copy(ident))
            {
                if let Some(mut val) = val {
                    val.attributes.0.extend(attributes.0);
                    return Ok(val);
                } else {
                    return Ok(Val {
                        value: Spanned::new(path.span(), Value::Unit),
                        attributes: Spanned::new(path.span().sub_span(0..0), Default::default()),
                    });
                }
            } else {
                Value::Ref(symbols.resolve_asset(path)?)
            }
        }
        parse::Value::Path(path) => match symbols.resolve_type(path) {
            Ok((val, type_path)) => match val {
                TypeKind::Any(_) => Value::Struct(Some(type_path), FieldsKind::Unit),
                TypeKind::Struct(Struct {
                    kind: DataFieldsKind::Unit,
                    ..
                }) => Value::Struct(Some(type_path), FieldsKind::Unit),
                TypeKind::EnumVariant(EnumVariant {
                    kind: DataFieldsKind::Unit,
                    variant,
                    ..
                }) => Value::Enum(
                    type_path,
                    variant.spanned(path.last.span()),
                    FieldsKind::Unit,
                ),
                TypeKind::Struct(Struct {
                    kind: DataFieldsKind::Struct(_),
                    ..
                })
                | TypeKind::EnumVariant(EnumVariant {
                    kind: DataFieldsKind::Struct(_),
                    ..
                }) => {
                    return Err(ConversionError::ExpectedFields.spanned(path.span()));
                }
                TypeKind::Struct(Struct {
                    kind: DataFieldsKind::Tuple(_),
                    ..
                })
                | TypeKind::EnumVariant(EnumVariant {
                    kind: DataFieldsKind::Tuple(_),
                    ..
                }) => {
                    return Err(ConversionError::ExpectedTupleFields.spanned(path.span()));
                }
                TypeKind::BitField(bitfield) => {
                    Value::BitFlags(Some(type_path), vec![bitfield.variant.spanned(path.span())])
                }
            },
            Err(conversion_error) => {
                if path.is_just("None") {
                    Value::Opt(None)
                } else {
                    return Err(conversion_error);
                }
            }
        },
        parse::Value::Map(map) => Value::Map(
            map.iter()
                .map(|(key, value)| {
                    Ok((
                        convert_value(key, symbols, add_value, false, object_name)?,
                        convert_value(value, symbols, add_value, false, object_name)?,
                    ))
                })
                .try_collect()?,
        ),
        parse::Value::Struct { name, fields } => {
            let fields = FieldsKind::Struct(
                fields
                    .iter()
                    .map(|(field, value)| {
                        Ok((
                            field.clone(),
                            convert_value(value, symbols, add_value, false, object_name)?,
                        ))
                    })
                    .try_collect()?,
            );
            match name {
                Some(path) => match symbols.resolve_type(path) {
                    Ok((val, type_path)) => match val {
                        TypeKind::Any(_) => Value::Struct(Some(type_path), fields),
                        // TODO: Check the fields here
                        TypeKind::Struct(Struct {
                            kind: DataFieldsKind::Struct(_),
                            ..
                        }) => Value::Struct(Some(type_path), fields),
                        TypeKind::EnumVariant(EnumVariant {
                            kind: DataFieldsKind::Struct(_),
                            variant,
                            ..
                        }) => Value::Enum(type_path, variant.spanned(path.last.span()), fields),
                        TypeKind::Struct(Struct {
                            kind: DataFieldsKind::Unit,
                            ..
                        })
                        | TypeKind::EnumVariant(EnumVariant {
                            kind: DataFieldsKind::Unit,
                            ..
                        }) => {
                            return Err(ConversionError::ExpectedUnit.spanned(path.span()));
                        }
                        TypeKind::Struct(Struct {
                            kind: DataFieldsKind::Tuple(_),
                            ..
                        })
                        | TypeKind::EnumVariant(EnumVariant {
                            kind: DataFieldsKind::Tuple(_),
                            ..
                        }) => {
                            return Err(ConversionError::ExpectedTupleFields.spanned(path.span()));
                        }
                        TypeKind::BitField(_) => {
                            return Err(ConversionError::ExpectedType.spanned(path.span()));
                        }
                    },
                    Err(err) => return Err(err),
                },
                None => Value::Struct(None, fields),
            }
        }
        parse::Value::Tuple { name, fields } => {
            let fields = fields
                .iter()
                .map(|val| convert_value(val, symbols, add_value, false, object_name))
                .try_collect()?;
            match name {
                Some(path) => match symbols.resolve_type(path) {
                    Ok((val, type_path)) => match val {
                        TypeKind::Any(_) => {
                            Value::Struct(Some(type_path), FieldsKind::Tuple(fields))
                        }
                        // TODO: Check the fields here
                        TypeKind::Struct(Struct {
                            kind: DataFieldsKind::Tuple(_),
                            ..
                        }) => Value::Struct(Some(type_path), FieldsKind::Tuple(fields)),
                        TypeKind::EnumVariant(EnumVariant {
                            kind: DataFieldsKind::Tuple(_),
                            variant,
                            ..
                        }) => Value::Enum(
                            type_path,
                            variant.spanned(path.last.span()),
                            FieldsKind::Tuple(fields),
                        ),
                        TypeKind::Struct(Struct {
                            kind: DataFieldsKind::Unit,
                            ..
                        })
                        | TypeKind::EnumVariant(EnumVariant {
                            kind: DataFieldsKind::Unit,
                            ..
                        }) => {
                            return Err(ConversionError::ExpectedUnit.spanned(path.span()));
                        }
                        TypeKind::Struct(Struct {
                            kind: DataFieldsKind::Struct(_),
                            ..
                        })
                        | TypeKind::EnumVariant(EnumVariant {
                            kind: DataFieldsKind::Struct(_),
                            ..
                        }) => {
                            return Err(ConversionError::ExpectedFields.spanned(path.span()));
                        }
                        TypeKind::BitField(_) => {
                            return Err(ConversionError::ExpectedType.spanned(path.span()));
                        }
                    },
                    Err(conversion_error) => {
                        if path.is_just("Some") {
                            let mut fields = fields.into_iter();
                            if fields.len() == 1 {
                                Value::Opt(fields.next().map(Box::new))
                            } else {
                                return Err(
                                    ConversionError::TooManyArguments.spanned(path.last.span())
                                );
                            }
                        } else {
                            return Err(conversion_error);
                        }
                    }
                },
                None => Value::Tuple(None, fields),
            }
        }
        parse::Value::Array(arr) => {
            // TODO: Check for type?
            Value::Array(
                arr.iter()
                    .map(|val| convert_value(val, symbols, add_value, false, object_name))
                    .try_collect()?,
            )
        }
        parse::Value::Or(values) => {
            let mut type_info = None::<TypePath>;
            let values = values
                .iter()
                .map(|path| {
                    let bitfield = symbols.resolve_bitfield(path)?;
                    if let Some(type_info) = &type_info {
                        if type_info.value == bitfield.type_info {
                            Ok(bitfield.value.variant.spanned(path.span()))
                        } else {
                            Err(ConversionError::ExpectedExactType(type_info.value.clone())
                                .spanned(path.span()))
                        }
                    } else {
                        type_info = Some(bitfield.value.type_info.spanned(bitfield.span));
                        Ok(bitfield.value.variant.spanned(path.span()))
                    }
                })
                .try_collect::<Vec<_>>()?;

            Value::BitFlags(type_info, values)
        }
        // parse::Value::Error => return Err(ConversionError::ParseError.spanned(value.value.span())),
        parse::Value::Unit => Value::Unit,
        parse::Value::Raw(data) => Value::Raw(data.clone()),
    };

    let mut val = Val {
        value: val.spanned(value.value.span()),
        attributes: attributes.spanned(value.attributes.span()),
    };

    if add_new_value {
        val = add_value(object_name, val);
    }

    Ok(val)
}

/// Converts a parsed value to a object value. With a conversion context and existing symbols. Also does some rudementory checking if the symbols are okay.
fn convert_object<C: AssetContext>(
    path: &str,
    name: &str,
    value: &ParseObject,
    symbols: &Symbols<C>,
    add_value: &mut impl FnMut(&str, Val) -> Val,
) -> Result<Object> {
    let value = convert_value(value, symbols, add_value, true, name)?;

    Ok(create_object(path, name, value))
}

fn create_object(path: &str, name: &str, value: Val) -> Object {
    Object {
        object_path: format!("{path}::{name}"),
        type_path: None,
        path: path.to_string(),
        value,
    }
}
