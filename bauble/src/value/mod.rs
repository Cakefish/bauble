use std::{borrow::Cow, collections::HashMap, error::Error, fmt::Display};

use indexmap::IndexMap;
use rust_decimal::Decimal;

use crate::{
    parse::{self, Object as ParseObject, Path, PathEnd, PathTreeEnd, Use, Values},
    spanned::{SpanExt, Spanned},
    VariantKind,
};

mod asset_context;

pub use asset_context::*;

#[derive(Clone)]
pub struct Attributes(pub IndexMap<Spanned<String>, Val>);

#[derive(Clone)]
/// A value with attributes
pub struct Val {
    pub value: Spanned<Value>,
    pub attributes: Spanned<Attributes>,
}

pub type Ident = Spanned<String>;

pub type Map = Vec<(Val, Val)>;

pub type Fields = IndexMap<Ident, Val>;

pub type Sequence = Vec<Val>;

// type path.
type TypePath = TypeInfo;

type AssetPath = String;

#[derive(Clone)]
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

#[derive(Clone)]
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

    pub fn type_info(&self) -> Option<&TypeInfo> {
        match self {
            Self::Struct(type_info, _) | Self::BitFlags(type_info, _) => type_info.as_ref(),
            Self::Enum(type_info, _, _) => Some(type_info),
            _ => None,
        }
    }
}

pub struct Object {
    pub object_path: AssetPath,
    pub type_path: Option<TypePath>,
    pub path: String,
    pub value: Val,
}

#[derive(Debug, PartialEq, Eq)]
pub enum ConversionError {
    ModuleNotFound,
    TypeNotFound,
    ObjectNotFound,
    AmbigousUse,
    UnknownAttribute,
    ExpectedIdent,
    MissingNameAttribute,
    ExpectedExpliciteType,
    ExpectedEnum,
    ExpectedUnit,
    ExpectedTupleFields,
    ExpectedFields,
    ExpectedBitfield,
    UnknownVariant,
    NotAnEnum,
    UnexpectedIdent,
    TooManyArguments,
    ExpectedAsset,
    ExpectedType,
    ExpectedExactType(TypeInfo),
    CopyCycle,
    ParseError,
}

impl Display for ConversionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use ConversionError::*;

        match self {
            ModuleNotFound => write!(f, "module not found"),
            TypeNotFound => write!(f, "type not found"),
            ObjectNotFound => write!(f, "object not found"),
            AmbigousUse => write!(f, "ambigous use"),
            UnknownAttribute => write!(f, "unknown attribute"),
            ExpectedIdent => write!(f, "expected identifier"),
            MissingNameAttribute => write!(f, "missing name attribute"),
            ExpectedExpliciteType => write!(f, "expected explicite type"),
            ExpectedEnum => write!(f, "expected enum"),
            ExpectedUnit => write!(f, "expected unit"),
            ExpectedTupleFields => write!(f, "expected tuple fields"),
            ExpectedFields => write!(f, "expected fields"),
            ExpectedBitfield => write!(f, "expected bitfield"),
            UnknownVariant => write!(f, "unknown variant"),
            NotAnEnum => write!(f, "not an enum"),
            UnexpectedIdent => write!(f, "unexpected identifier"),
            TooManyArguments => write!(f, "too many arguments"),
            ExpectedAsset => write!(f, "expected asset"),
            ExpectedType => write!(f, "expected type"),
            ExpectedExactType(type_info) => {
                write!(f, "expected type {type_info}")
            }
            CopyCycle => write!(f, "Copy cycle"),
            ParseError => write!(f, "Parse error"),
        }
    }
}

impl Error for ConversionError {}

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
            RefCopy::Unresolved | RefCopy::Resolved(_) => Err(ConversionError::AmbigousUse),
            RefCopy::Ref(reference) => Ok(RefCopy::Ref(
                reference
                    .combined(other)
                    .ok_or(ConversionError::AmbigousUse)?,
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
                                .map_err(|e| e.span(end.span))?;
                        }
                    } else {
                        return Err(ConversionError::ModuleNotFound.span(end.span));
                    }
                }
                PathTreeEnd::PathEnd(PathEnd::Ident(ident)) => {
                    let path = format!("{leading}::{ident}");
                    if let Some(reference) = this.ctx.get_ref(&path) {
                        this.add_ref(ident.value.clone(), reference)
                            .map_err(|e| e.span(ident.span))?;
                    } else {
                        return Err(ConversionError::ModuleNotFound.span(end.span));
                    }
                }
                PathTreeEnd::PathEnd(PathEnd::WithIdent(ident)) => {
                    if let Some(reference) = this.ctx.with_ident(&leading, ident.as_str()) {
                        this.add_ref(ident.value.clone(), reference)
                            .map_err(|e| e.span(ident.span))?;
                    } else {
                        return Err(ConversionError::ModuleNotFound.span(end.span));
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

    fn try_resolve_macro<'a>(&'a self, ident: &str) -> Option<(&'a str, Option<Val>)> {
        let (key, value) = self.uses.get_key_value(ident)?;
        match value {
            RefCopy::Unresolved => Some((key, None)),
            RefCopy::Resolved(val) => Some((key, Some(val.clone()))),
            RefCopy::Ref(_) => None,
        }
    }

    fn get_module(&self, ident: &str) -> Option<&str> {
        self.uses
            .get(ident)
            .and_then(|reference| reference.unwrap_ref().get_module())
    }

    fn resolve_item(&self, path: &Path) -> Result<Cow<Reference>> {
        if let (true, Some(asset)) = (
            path.leading.is_empty(),
            match &path.last.value {
                PathEnd::Ident(ident) => self.uses.get(ident.as_str()),
                PathEnd::WithIdent(_) => None,
            },
        ) {
            Ok(Cow::Borrowed(asset.unwrap_ref()))
        } else if path.leading.is_empty() {
            Ok(Cow::Owned(match &path.last.value {
                PathEnd::WithIdent(ident) => self
                    .ctx
                    .with_ident("", ident.as_str())
                    .ok_or(ConversionError::UnexpectedIdent.span(path.last.span))?,
                PathEnd::Ident(ident) => self
                    .ctx
                    .get_ref(ident.as_str())
                    .ok_or(ConversionError::UnexpectedIdent.span(path.last.span))?,
            }))
        } else {
            let first = path.leading.first().expect("We know the Vec isn't empty.");
            let mut p = self
                .get_module(first.as_str())
                .unwrap_or(first.as_str())
                .to_string();

            for ident in &path.leading[1..] {
                p.push_str("::");
                p.push_str(ident.as_str());
            }

            Ok(Cow::Owned(match &path.last.value {
                PathEnd::WithIdent(ident) => self
                    .ctx
                    .with_ident(&p, ident.as_str())
                    .ok_or(ConversionError::UnexpectedIdent.span(path.last.span))?,
                PathEnd::Ident(ident) => {
                    p.push_str("::");
                    p.push_str(ident.as_str());
                    self.ctx
                        .get_ref(&p)
                        .ok_or(ConversionError::UnexpectedIdent.span(path.last.span))?
                }
            }))
        }
    }

    fn resolve_asset(&self, path: &Spanned<Path>) -> Result<String> {
        let item = self.resolve_item(path)?;

        item.into_owned()
            .to_asset()
            .ok_or(ConversionError::ExpectedAsset.span(path.span))
    }

    fn resolve_type(&self, path: &Spanned<Path>) -> Result<TypeKind> {
        let item = self.resolve_item(path)?;

        item.into_owned()
            .to_type()
            .ok_or(ConversionError::ExpectedType.span(path.span))
    }

    fn resolve_bitfield(&self, path: &Spanned<Path>) -> Result<BitField> {
        let item = self.resolve_type(path)?;

        if let TypeKind::BitField(bitfield) = item {
            Ok(bitfield)
        } else {
            Err(ConversionError::ExpectedBitfield.span(path.span))
        }
    }
}

pub fn convert_values<C: AssetContext>(
    path: String,
    values: Values,
    default_symbols: &Symbols<C>,
) -> Result<Vec<Object>> {
    let mut use_symbols = Symbols::new(&default_symbols.ctx);
    for use_ in values.uses {
        use_symbols.add_use(&use_)?;
    }

    let mut symbols = default_symbols.clone();

    for (symbol, _) in &values.values {
        let path = format!("{path}::{symbol}");
        symbols
            .add_ref(
                symbol.value.clone(),
                Reference::Specific {
                    ty: None,
                    asset: Some(path),
                    module: None,
                },
            )
            .map_err(|e| e.span(symbol.span))?;
    }
    symbols.add(use_symbols);

    for (symbol, _) in &values.copies {
        symbols
            .uses
            .insert(symbol.value.clone(), RefCopy::Unresolved);
    }

    let mut spans = HashMap::new();
    let mut copy_graph = petgraph::graphmap::DiGraphMap::new();

    for (symbol, value) in &values.copies {
        spans.insert(symbol.as_str(), symbol.span);
        copy_graph.add_node(symbol.as_str());
        find_copy_refs(value, &symbols, &mut |s| {
            copy_graph.add_edge(s, symbol.as_str(), ());
        });
    }

    let order = petgraph::algo::toposort(&copy_graph, None)
        .map_err(|err| ConversionError::CopyCycle.span(spans[err.node_id()]))?
        .into_iter()
        .map(|s| s.to_string())
        .collect::<Vec<_>>();

    for item in order {
        let val = convert_value(&values.copies[item.as_str()], &symbols)?;

        symbols.uses.insert(item, RefCopy::Resolved(val));
    }

    values
        .values
        .iter()
        .map(|value| convert_object(&path, &value.0.value, value.1, &symbols))
        .try_collect()
}

fn find_copy_refs<'a, C: AssetContext>(
    object: &ParseObject,
    symbols: &'a Symbols<C>,
    found: &mut impl FnMut(&'a str),
) {
    for obj in object.attributes.0.values() {
        find_copy_refs(obj, symbols, found)
    }

    match &object.value.value {
        parse::Value::Ref(reference) => {
            if let Some(ident) = reference.as_ident() {
                if let Some((ident, _)) = symbols.try_resolve_macro(ident) {
                    found(ident)
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

fn convert_value<C: AssetContext>(value: &ParseObject, symbols: &Symbols<C>) -> Result<Val> {
    let attributes = Attributes(
        value
            .attributes
            .0
            .iter()
            .map(|(ident, value)| Ok((ident.clone(), convert_value(value, symbols)?)))
            .try_collect()?,
    );

    let val = match &value.value.value {
        parse::Value::Num(num) => Value::Num(*num),
        parse::Value::Bool(b) => Value::Bool(*b),
        parse::Value::Str(s) => Value::Str(s.clone()),
        parse::Value::Ref(path) => {
            if let Some((_, val)) = path
                .as_ident()
                .and_then(|ident| symbols.try_resolve_macro(ident))
            {
                if let Some(mut val) = val {
                    val.attributes.0.extend(attributes.0);
                    return Ok(val);
                } else {
                    return Err(ConversionError::CopyCycle.span(path.span));
                }
            } else {
                Value::Ref(symbols.resolve_asset(path)?)
            }
        }
        parse::Value::Path(path) => match symbols.resolve_type(path) {
            Ok(val) => match val {
                TypeKind::Any(ty) => Value::Struct(Some(ty), FieldsKind::Unit),
                TypeKind::Struct(Struct {
                    kind: DataFields::Unit,
                    type_info,
                }) => Value::Struct(Some(type_info), FieldsKind::Unit),
                TypeKind::EnumVariant(EnumVariant {
                    kind: DataFields::Unit,
                    enum_type_info,
                    variant,
                }) => Value::Enum(
                    enum_type_info,
                    variant.span(path.last.span),
                    FieldsKind::Unit,
                ),
                TypeKind::Struct(Struct {
                    kind: DataFields::Struct(_),
                    ..
                })
                | TypeKind::EnumVariant(EnumVariant {
                    kind: DataFields::Struct(_),
                    ..
                }) => {
                    return Err(ConversionError::ExpectedFields.span(path.span));
                }
                TypeKind::Struct(Struct {
                    kind: DataFields::Tuple(_),
                    ..
                })
                | TypeKind::EnumVariant(EnumVariant {
                    kind: DataFields::Tuple(_),
                    ..
                }) => {
                    return Err(ConversionError::ExpectedTupleFields.span(path.span));
                }
                TypeKind::BitField(bitfield) => Value::BitFlags(
                    Some(bitfield.type_info),
                    vec![bitfield.variant.span(path.span)],
                ),
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
                    Ok((convert_value(key, symbols)?, convert_value(value, symbols)?))
                })
                .try_collect()?,
        ),
        parse::Value::Struct { name, fields } => {
            let fields = FieldsKind::Struct(
                fields
                    .iter()
                    .map(|(field, value)| Ok((field.clone(), convert_value(value, symbols)?)))
                    .try_collect()?,
            );
            match name {
                Some(path) => match symbols.resolve_type(path) {
                    Ok(val) => match val {
                        TypeKind::Any(ty) => Value::Struct(Some(ty), fields),
                        // TODO: Check the fields here
                        TypeKind::Struct(Struct {
                            kind: DataFields::Struct(_),
                            type_info,
                        }) => Value::Struct(Some(type_info), fields),
                        TypeKind::EnumVariant(EnumVariant {
                            kind: DataFields::Struct(_),
                            enum_type_info,
                            variant,
                        }) => Value::Enum(enum_type_info, variant.span(path.last.span), fields),
                        TypeKind::Struct(Struct {
                            kind: DataFields::Unit,
                            ..
                        })
                        | TypeKind::EnumVariant(EnumVariant {
                            kind: DataFields::Unit,
                            ..
                        }) => {
                            return Err(ConversionError::ExpectedUnit.span(path.span));
                        }
                        TypeKind::Struct(Struct {
                            kind: DataFields::Tuple(_),
                            ..
                        })
                        | TypeKind::EnumVariant(EnumVariant {
                            kind: DataFields::Tuple(_),
                            ..
                        }) => {
                            return Err(ConversionError::ExpectedTupleFields.span(path.span));
                        }
                        TypeKind::BitField(_) => {
                            return Err(ConversionError::ExpectedType.span(path.span))
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
                .map(|val| convert_value(val, symbols))
                .try_collect()?;
            match name {
                Some(path) => match symbols.resolve_type(path) {
                    Ok(val) => match val {
                        TypeKind::Any(ty) => Value::Struct(Some(ty), FieldsKind::Tuple(fields)),
                        // TODO: Check the fields here
                        TypeKind::Struct(Struct {
                            kind: DataFields::Tuple(_),
                            type_info,
                        }) => Value::Struct(Some(type_info), FieldsKind::Tuple(fields)),
                        TypeKind::EnumVariant(EnumVariant {
                            kind: DataFields::Tuple(_),
                            enum_type_info,
                            variant,
                        }) => Value::Enum(
                            enum_type_info,
                            variant.span(path.last.span),
                            FieldsKind::Tuple(fields),
                        ),
                        TypeKind::Struct(Struct {
                            kind: DataFields::Unit,
                            ..
                        })
                        | TypeKind::EnumVariant(EnumVariant {
                            kind: DataFields::Unit,
                            ..
                        }) => {
                            return Err(ConversionError::ExpectedUnit.span(path.span));
                        }
                        TypeKind::Struct(Struct {
                            kind: DataFields::Struct(_),
                            ..
                        })
                        | TypeKind::EnumVariant(EnumVariant {
                            kind: DataFields::Struct(_),
                            ..
                        }) => {
                            return Err(ConversionError::ExpectedFields.span(path.span));
                        }
                        TypeKind::BitField(_) => {
                            return Err(ConversionError::ExpectedType.span(path.span))
                        }
                    },
                    Err(conversion_error) => {
                        if path.is_just("Some") {
                            let mut fields = fields.into_iter();
                            if fields.len() == 1 {
                                Value::Opt(fields.next().map(Box::new))
                            } else {
                                return Err(ConversionError::TooManyArguments.span(path.last.span));
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
                    .map(|val| convert_value(val, symbols))
                    .try_collect()?,
            )
        }
        parse::Value::Or(values) => {
            let mut type_info = None::<TypeInfo>;
            let values = values
                .iter()
                .map(|path| {
                    let bitfield = symbols.resolve_bitfield(path)?;
                    if let Some(type_info) = &type_info {
                        if *type_info == bitfield.type_info {
                            Ok(bitfield.variant.span(path.span))
                        } else {
                            Err(ConversionError::ExpectedExactType(type_info.clone())
                                .span(path.span))
                        }
                    } else {
                        type_info = Some(bitfield.type_info);
                        Ok(bitfield.variant.span(path.span))
                    }
                })
                .try_collect::<Vec<_>>()?;

            Value::BitFlags(type_info, values)
        }
        parse::Value::Error => return Err(ConversionError::ParseError.span(value.value.span)),
        parse::Value::Unit => Value::Unit,
        parse::Value::Raw(data) => Value::Raw(data.clone()),
    };

    Ok(Val {
        value: val.span(value.value.span),
        attributes: attributes.span(value.attributes.span),
    })
}

/// Converts a parsed value to a object value. With a convertion context and existing symbols. Also does some rudementory checking if the symbols are okay.
fn convert_object<C: AssetContext>(
    path: &str,
    name: &str,
    value: &ParseObject,
    symbols: &Symbols<C>,
) -> Result<Object> {
    let value = convert_value(value, symbols)?;

    Ok(Object {
        // TODO: Create an object path.
        object_path: name.to_string(),
        type_path: value.value.type_info().cloned(),
        path: path.to_string(),
        value,
    })
}
