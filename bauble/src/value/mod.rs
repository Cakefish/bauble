use std::{
    borrow::Cow,
    collections::{HashMap, HashSet},
};

use indexmap::IndexMap;
use rust_decimal::Decimal;

use crate::{
    AssetContext, BaubleError, BaubleErrors, FileId, VariantKind,
    bauble_context::PathReference,
    error::Level,
    parse::{self, Object as ParseObject, Path, PathEnd, PathTreeEnd, Use, Values},
    path::{TypePath, TypePathElem},
    spanned::{SpanExt, Spanned},
    types::{self, TypeId},
};

#[derive(Clone, Debug, Default)]
pub struct Attributes<Inner = Val>(pub IndexMap<Spanned<String>, Inner>);

#[derive(Clone, Debug)]
/// A value with attributes
pub struct Val {
    pub ty: TypeId,
    pub value: Spanned<Value>,
    pub attributes: Spanned<Attributes>,
}

#[derive(Clone)]
enum CopyVal {
    Copy {
        ty: Option<Spanned<TypeId>>,
        value: Spanned<Value<CopyVal>>,
        attributes: Spanned<Attributes<CopyVal>>,
    },
    Resolved(Val),
}

#[derive(Clone, Copy)]
enum BorrowCopyVal<'a> {
    Copy {
        ty: &'a Option<Spanned<TypeId>>,
        value: &'a Spanned<Value<CopyVal>>,
        attributes: &'a Spanned<Attributes<CopyVal>>,
    },
    Resolved(&'a Val),
}

impl<'a> From<&'a CopyVal> for BorrowCopyVal<'a> {
    fn from(value: &'a CopyVal) -> Self {
        match value {
            CopyVal::Copy {
                ty,
                value,
                attributes,
            } => BorrowCopyVal::Copy {
                ty,
                value,
                attributes,
            },
            CopyVal::Resolved(val) => BorrowCopyVal::Resolved(val),
        }
    }
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

pub type Fields<Inner = Val> = IndexMap<Ident, Inner>;

pub type Sequence<Inner = Val> = Vec<Inner>;

#[derive(Clone, Debug)]
pub enum FieldsKind<Inner = Val> {
    Unit,
    Unnamed(Sequence<Inner>),
    Named(Fields<Inner>),
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

#[derive(Clone, Debug)]
pub enum PrimitiveValue {
    Num(Decimal),
    Str(String),
    Bool(bool),
    Unit,
    Raw(String),
}

#[derive(Clone, Debug)]
pub enum Value<Inner = Val> {
    // Fully resolved path.
    Ref(TypePath),

    Tuple(Sequence<Inner>),
    Array(Sequence<Inner>),
    Map(Map<Inner>),

    /// Either struct or enum variant
    Struct(FieldsKind<Inner>),

    BitFlags(Vec<Spanned<TypePathElem>>),

    Primitive(PrimitiveValue),

    Transparent(Box<Inner>),

    Enum(Spanned<TypePathElem>, Box<Inner>),
}

#[derive(Debug)]
pub struct Object {
    pub object_path: TypePath,
    pub value: Val,
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
    ExpectedExactType(TypeId),
    PathError(crate::path::PathError),
    CopyCycle(Vec<(Spanned<String>, Vec<Spanned<String>>)>),
}

impl ConversionError {
    fn expected_ty(ty: Spanned<TypeId>) -> Spanned<ConversionError> {
        ty.map(ConversionError::ExpectedExactType)
    }
}

impl From<crate::path::PathError> for ConversionError {
    fn from(value: crate::path::PathError) -> Self {
        Self::PathError(value)
    }
}

impl BaubleError for Spanned<ConversionError> {
    fn msg_general(&self, _types: &types::TypeRegistry) -> crate::error::ErrorMsg {
        let msg = match &self.value {
            ConversionError::CopyCycle(_) => "A copy cycle was found",
            ConversionError::PathError(_) => "Path error",
            _ => "Conversion error",
        };

        Cow::Borrowed(msg).spanned(self.span)
    }

    fn msgs_specific(
        &self,
        types: &types::TypeRegistry,
    ) -> Vec<(crate::error::ErrorMsg, crate::error::Level)> {
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
            ConversionError::ExpectedExactType(ty) => {
                return vec![(
                    Cow::<str>::Owned(format!(
                        "Expected the type `{}`",
                        types.key_type(*ty).meta.path
                    ))
                    .spanned(self.span),
                    Level::Error,
                )];
            }
            ConversionError::PathError(err) => {
                let generic = match err {
                    crate::path::PathError::EmptyElem(_) => "Malformed path",
                    crate::path::PathError::MissingEnd(_) => "Malformed path",
                    crate::path::PathError::MissingStart(_) => "Malformed path",
                    crate::path::PathError::TooManyElements => "Path had too many elements",
                    crate::path::PathError::ZeroElements => "Path had no elements",
                };

                let mut errors = vec![(Cow::Borrowed(generic).spanned(self.span), Level::Error)];

                let span_index = |i| self.span.sub_span(i..i + 1);

                match err {
                    crate::path::PathError::EmptyElem(i) => {
                        errors.push((
                            Cow::Borrowed("There should be a non-empty path element here")
                                .spanned(span_index(*i)),
                            Level::Error,
                        ));
                    }
                    crate::path::PathError::MissingEnd(i) => {
                        errors.push((
                            Cow::Borrowed("This delimiter is missing a closing delimiter")
                                .spanned(span_index(*i)),
                            Level::Error,
                        ));
                    }
                    crate::path::PathError::MissingStart(i) => {
                        errors.push((
                            Cow::Borrowed("This delimiter is missing an opening delimiter")
                                .spanned(span_index(*i)),
                            Level::Error,
                        ));
                    }
                    _ => {}
                };

                return errors;
            }
            ConversionError::CopyCycle(cycle) => {
                return cycle
                    .iter()
                    .flat_map(|(a, contained)| {
                        std::iter::once((
                            Cow::<str>::Owned(format!("`{a}` which depends on")).spanned(a.span),
                            Level::Error,
                        ))
                        .chain(contained.iter().map(|b| {
                            (
                                Cow::<str>::Owned(format!("`${b}` here")).spanned(b.span),
                                Level::Error,
                            )
                        }))
                    })
                    .collect();
            }
        };

        vec![(Cow::Borrowed(msg).spanned(self.span), Level::Error)]
    }
}

type Result<T> = std::result::Result<T, Spanned<ConversionError>>;

impl From<Spanned<crate::path::PathError>> for Spanned<ConversionError> {
    fn from(value: Spanned<crate::path::PathError>) -> Self {
        value.map(ConversionError::PathError)
    }
}

#[derive(Clone)]
enum RefCopy {
    Unresolved,
    Resolved(CopyVal),
    Ref(PathReference),
}

impl Default for RefCopy {
    fn default() -> Self {
        Self::Ref(Default::default())
    }
}

impl RefCopy {
    /// # Panics
    /// Panics if self isn't a reference.
    fn unwrap_ref(&self) -> &PathReference {
        match self {
            RefCopy::Ref(r) => r,
            RefCopy::Unresolved | RefCopy::Resolved(_) => panic!("Not a reference"),
        }
    }

    fn add(self, other: PathReference) -> std::result::Result<Self, ConversionError> {
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
    uses: HashMap<TypePathElem, RefCopy>,
}

impl<C: AssetContext> Symbols<C> {
    pub fn new(ctx: C) -> Self {
        Self {
            ctx,
            uses: HashMap::default(),
        }
    }
    pub fn cloned(&self) -> Symbols<&C> {
        Symbols {
            ctx: &self.ctx,
            uses: self.uses.clone(),
        }
    }

    fn add_ref(
        &mut self,
        ident: TypePathElem,
        reference: PathReference,
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
            leading: TypePath,
            end: &Spanned<PathTreeEnd>,
        ) -> Result<()> {
            match &end.value {
                PathTreeEnd::Group(g) => {
                    for node in g {
                        let mut leading = leading.clone();
                        for s in &node.leading.value {
                            leading.push_str(&s.value).map_err(|e| e.spanned(s.span))?;
                        }
                        add_use_inner(this, leading, &node.end)?;
                    }
                }
                PathTreeEnd::Everything => {
                    if let Some(uses) = this.ctx.all_in(leading.borrow()) {
                        for (ident, reference) in uses {
                            this.add_ref(ident, reference)
                                .map_err(|e| e.spanned(end.span))?;
                        }
                    } else {
                        return Err(ConversionError::ModuleNotFound.spanned(end.span));
                    }
                }
                PathTreeEnd::PathEnd(PathEnd::Ident(ident)) => {
                    let path_end =
                        TypePathElem::new(ident.as_str()).map_err(|e| e.spanned(ident.span))?;
                    let path = leading.combine(&path_end);
                    if let Some(reference) = this.ctx.get_ref(path.borrow()) {
                        this.add_ref(path_end.to_owned(), reference)
                            .map_err(|e| e.spanned(ident.span))?;
                    } else {
                        return Err(ConversionError::ModuleNotFound.spanned(end.span));
                    }
                }
                PathTreeEnd::PathEnd(PathEnd::WithIdent(ident)) => {
                    let path_end =
                        TypePathElem::new(ident.as_str()).map_err(|e| e.spanned(ident.span))?;
                    if let Some(reference) = this.ctx.with_ident(leading.borrow(), path_end) {
                        this.add_ref(path_end.to_owned(), reference)
                            .map_err(|e| e.spanned(ident.span))?;
                    } else {
                        return Err(ConversionError::ModuleNotFound.spanned(end.span));
                    }
                }
            }
            Ok(())
        }

        let mut leading = TypePath::empty();
        for l in use_.leading.iter() {
            leading.push_str(l).map_err(|e| e.spanned(l.span))?;
        }
        add_use_inner(self, leading, &use_.end)
    }

    fn try_resolve_copy<'a>(
        &'a self,
        ident: &str,
    ) -> Option<(TypePathElem<&'a str>, Option<&'a CopyVal>)> {
        let (key, value) = self.uses.get_key_value(ident)?;
        match value {
            RefCopy::Unresolved => Some((key.borrow(), None)),
            RefCopy::Resolved(val) => Some((key.borrow(), Some(val))),
            RefCopy::Ref(_) => None,
        }
    }

    fn get_module(&self, ident: &str) -> Option<TypePath> {
        self.uses
            .get(ident)
            .and_then(|reference| reference.unwrap_ref().module.clone())
    }

    fn resolve_item(&self, path: &Path) -> Result<Cow<PathReference>> {
        if path.leading.is_empty() {
            match &path.last.value {
                PathEnd::Ident(ident) => {
                    if let Some(asset) = self.uses.get(ident.as_str()) {
                        Ok(Cow::Borrowed(asset.unwrap_ref()))
                    } else {
                        self.ctx
                            .get_ref(
                                TypePath::new(ident.as_str()).expect("Parsed path is malformed"),
                            )
                            .ok_or(ConversionError::UnexpectedIdent.spanned(path.last.span))
                            .map(Cow::Owned)
                    }
                }
                PathEnd::WithIdent(ident) => self
                    .ctx
                    .with_ident(
                        TypePath::empty(),
                        TypePathElem::new(ident.as_str()).expect("Parsed path is malformed"),
                    )
                    .ok_or(ConversionError::UnexpectedIdent.spanned(path.last.span))
                    .map(Cow::Owned),
            }
        } else {
            let first = path.leading.first().expect("We know the Vec isn't empty.");
            let mut p = self
                .get_module(first.as_str())
                .unwrap_or(TypePath::new(first.to_string()).map_err(|e| e.spanned(first.span))?);

            for ident in &path.leading[1..] {
                p.push_str(ident.as_str())
                    .map_err(|e| e.spanned(ident.span))?;
            }

            match &path.last.value {
                PathEnd::WithIdent(ident) => self
                    .ctx
                    .with_ident(
                        p.borrow(),
                        TypePathElem::new(ident.as_str()).map_err(|e| e.spanned(ident.span))?,
                    )
                    .ok_or(ConversionError::UnexpectedIdent.spanned(path.last.span)),
                PathEnd::Ident(ident) => {
                    p.push_str(ident.as_str())
                        .map_err(|e| e.spanned(ident.span))?;
                    self.ctx
                        .get_ref(p.borrow())
                        .ok_or(ConversionError::UnexpectedIdent.spanned(path.last.span))
                }
            }
            .map(Cow::Owned)
        }
    }

    fn resolve_asset(&self, path: &Spanned<Path>) -> Result<(TypeId, TypePath)> {
        let item = self.resolve_item(path)?;

        item.asset
            .clone()
            .ok_or(ConversionError::ExpectedAsset.spanned(path.span))
    }

    fn resolve_type(&self, path: &Spanned<Path>) -> Result<TypeId> {
        let item = self.resolve_item(path)?;

        item.ty
            .ok_or(ConversionError::ExpectedType.spanned(path.span))
    }
}

pub fn register_assets(
    path: TypePath<&str>,
    ctx: &mut crate::bauble_context::BaubleContext,
    default_uses: impl IntoIterator<Item = (TypePathElem, PathReference)>,
    values: &Values,
) -> std::result::Result<(), Vec<Spanned<ConversionError>>> {
    let mut uses = default_uses
        .into_iter()
        .map(|(key, val)| (key, RefCopy::Ref(val)))
        .collect();
    let mut errors = Vec::new();
    // TODO: Register these in a correct order...
    for (ident, binding) in &values.values {
        let ident = &TypePathElem::new(ident.as_str()).expect("Invariant");
        let path = path.combine(ident);
        let mut symbols = Symbols { ctx: &*ctx, uses };

        let ty = if let Some(ty) = &binding.type_path {
            symbols.resolve_type(ty)
        } else {
            value_type(&binding.object, &symbols)
                .transpose()
                .unwrap_or(Err(
                    ConversionError::ExpectedType.spanned(binding.object.value.span)
                ))
                .map(|t| t.value)
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
                    errors.push(e.spanned(binding.object.value.span));
                }
                Symbols { uses, .. } = symbols;
                ctx.register_asset(path, ty);
            }
            Err(err) => {
                Symbols { uses, .. } = symbols;
                errors.push(err)
            }
        };
    }

    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

pub fn convert_values<C: AssetContext>(
    file: FileId,
    values: Values,
    default_symbols: &Symbols<C>,
) -> std::result::Result<Vec<Object>, BaubleErrors> {
    let mut use_symbols = Symbols::new(&default_symbols.ctx);
    let mut use_errors = Vec::new();
    for use_ in values.uses {
        if let Err(e) = use_symbols.add_use(&use_) {
            use_errors.push(e);
        }
    }

    let mut symbols = default_symbols.cloned();

    let path = symbols.ctx.get_file_path(file);

    for (symbol, _) in &values.values {
        let ident = TypePathElem::new(symbol.as_str()).expect("Invariant");
        let path = path.combine(&ident);

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
            use_errors.push(ConversionError::ModuleNotFound.spanned(symbol.span));
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
        find_copy_refs(value, &symbols, &mut |s| {
            copy_graph.add_edge(symbol, s.value, ());
            contained_spans.entry(symbol).or_default().push(s);
        });
    }

    let mut objects = Vec::new();
    let mut name_allocs = HashMap::new();
    let mut add_value = |name: TypePathElem<&str>, val: Val| {
        let idx = *name_allocs
            .entry(name.to_owned())
            .and_modify(|i| *i += 1u64)
            .or_insert(0);
        let name = TypePathElem::new(format!("{name}@{idx}"))
            .expect("idx is just a number, and we know name is a valid path elem.");

        objects.push(create_object(path, name.borrow(), val));

        Value::Ref(path.combine(&name))
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
            ConversionError::CopyCycle(
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

    match petgraph::algo::toposort(&copy_graph, None) {
        Ok(order) => {
            let order = order.into_iter().map(|o| o.to_owned()).collect::<Vec<_>>();
            for item in order {
                let val = match convert_copy_value(
                    &values.copies[item.as_str()],
                    &symbols,
                    &mut add_value,
                    item.borrow(),
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

        match convert_object(path, ident, &binding.object, &symbols, ty, &mut add_value) {
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
    found: &mut impl FnMut(Spanned<TypePathElem<&'a str>>),
) {
    for obj in object.attributes.0.values() {
        find_copy_refs(obj, symbols, found)
    }

    match &object.value.value {
        parse::Value::Ref(reference) => {
            if let Some(ident) = reference.as_ident() {
                if let Some((ident, _)) = symbols.try_resolve_copy(ident) {
                    found(ident.spanned(reference.span))
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

#[derive(Clone, Copy)]
struct BorrowedObject<'a> {
    value: &'a Spanned<parse::Value>,
    attributes: &'a Spanned<parse::Attributes>,
}

impl<'a> From<&'a ParseObject> for BorrowedObject<'a> {
    fn from(value: &'a ParseObject) -> Self {
        BorrowedObject {
            value: &value.value,
            attributes: &value.attributes,
        }
    }
}

fn value_type<'a, C: AssetContext>(
    value: impl Into<BorrowedObject<'a>>,
    symbols: &Symbols<C>,
) -> Result<Option<Spanned<TypeId>>> {
    let value: BorrowedObject<'a> = value.into();
    let types = symbols.ctx.type_registry();
    let mut ty = match &value.value.value {
        parse::Value::Unit => Some(
            types
                .primitive_type(types::Primitive::Unit)
                .spanned(value.value.span),
        ),
        parse::Value::Num(_) => Some(
            types
                .primitive_type(types::Primitive::Num)
                .spanned(value.value.span),
        ),
        parse::Value::Bool(_) => Some(
            types
                .primitive_type(types::Primitive::Bool)
                .spanned(value.value.span),
        ),
        parse::Value::Str(_) => Some(
            types
                .primitive_type(types::Primitive::Str)
                .spanned(value.value.span),
        ),
        parse::Value::Ref(path) => {
            if let Some(ident) = path.as_ident()
                && let Some((_, Some(copy))) = symbols.try_resolve_copy(ident)
            {
                match copy {
                    CopyVal::Copy { ty, .. } => *ty,
                    CopyVal::Resolved(val) => Some(val.ty.spanned(val.value.span)),
                }
            } else {
                Some(symbols.resolve_asset(path)?.0.spanned(path.span))
            }
        }
        parse::Value::Path(path) => Some(symbols.resolve_type(path)?.spanned(value.value.span)),
        parse::Value::Map(_) => None,
        parse::Value::Struct { name, .. } | parse::Value::Tuple { name, .. } => name
            .as_ref()
            .map(|path| symbols.resolve_type(path).map(|t| t.spanned(path.span)))
            .transpose()?,
        parse::Value::Array(_) => None,
        parse::Value::Or(paths) => {
            let mut ty = None;
            for path in paths {
                let variant_ty = symbols.resolve_type(path)?;

                let enum_type = match &types.key_type(variant_ty).kind {
                    types::TypeKind::EnumVariant {
                        enum_type,
                        fields: types::Fields::Unit,
                        ..
                    } => Ok(*enum_type),
                    types::TypeKind::Generic(type_set) => {
                        if let Some(instance) = types.iter_type_set(type_set).next()
                            && let types::TypeKind::EnumVariant {
                                fields: types::Fields::Unit,
                                enum_type,
                                ..
                            } = &types.key_type(instance).kind
                        {
                            let enum_ty = types.key_type(*enum_type);

                            if !matches!(enum_ty.kind, types::TypeKind::BitFlags { .. }) {
                                // This could've been an enum too.
                                return Err(ConversionError::ExpectedBitfield.spanned(path.span));
                            }

                            if let Some(generic) = enum_ty.meta.generic_base_type {
                                Ok(generic.into())
                            } else {
                                debug_assert!(
                                    false,
                                    "If the variant has a generic type, the bitfield should too"
                                );

                                Err(ConversionError::ExpectedType.spanned(path.span))
                            }
                        } else {
                            // Generic type doesn't have any instances. Or the instance we got wasn't a bitfield.
                            Err(ConversionError::ExpectedBitfield.spanned(path.span))
                        }
                    }
                    _ => Err(ConversionError::ExpectedBitfield.spanned(path.span)),
                }?;

                match &mut ty {
                    Some(ty) => {
                        if Some(*ty)
                            == types
                                .key_type(enum_type)
                                .meta
                                .generic_base_type
                                .map(|t| t.into())
                        {
                            *ty = enum_type;
                        } else if !types.can_infer_from(*ty, enum_type) {
                            return Err(ConversionError::ExpectedExactType(*ty).spanned(path.span));
                        }
                    }
                    None => ty = Some(enum_type),
                }
            }

            ty.map(|t| t.spanned(value.value.span))
        }
        parse::Value::Raw(_) => None,
    };

    if let Some(Spanned { value: ty, .. }) = &mut ty {
        match &types.key_type(*ty).kind {
            types::TypeKind::EnumVariant { enum_type, .. } => {
                *ty = *enum_type;
            }
            types::TypeKind::Generic(set) => {
                if let Some(t) = types.iter_type_set(set).next()
                    && let types::TypeKind::EnumVariant { enum_type, .. } = &types.key_type(t).kind
                {
                    *ty = types
                        .key_type(*enum_type)
                        .meta
                        .generic_base_type
                        .expect("Invariant, if the EnumVariant is generic so is the enum type")
                        .into();
                }
            }
            _ => {}
        }
    }

    Ok(ty)
}

fn convert_copy_value<'a, C: AssetContext>(
    value: impl Into<BorrowedObject<'a>>,
    symbols: &Symbols<C>,
    add_value: &mut impl FnMut(TypePathElem<&str>, Val) -> Value,
    object_name: TypePathElem<&str>,
) -> Result<CopyVal> {
    let value: BorrowedObject<'a> = value.into();
    let types = symbols.ctx.type_registry();
    let val_type = value_type(value, symbols)?;

    if let Some(val_type) = val_type.as_ref()
        && types.key_type(val_type.value).kind.instanciable()
    {
        convert_value(value, symbols, add_value, val_type.value, object_name).map(CopyVal::Resolved)
    } else {
        let attributes = value
            .attributes
            .0
            .iter()
            .map(|(ident, value)| {
                Ok::<_, Spanned<ConversionError>>((
                    ident.clone(),
                    convert_copy_value(value, symbols, add_value, object_name)?,
                ))
            })
            .try_collect()?;
        let inner = match &value.value.value {
            parse::Value::Unit => Value::Primitive(PrimitiveValue::Unit),
            parse::Value::Num(decimal) => Value::Primitive(PrimitiveValue::Num(*decimal)),
            parse::Value::Bool(b) => Value::Primitive(PrimitiveValue::Bool(*b)),
            parse::Value::Str(s) => Value::Primitive(PrimitiveValue::Str(s.clone())),
            parse::Value::Ref(path) => Value::Ref(symbols.resolve_asset(path)?.1),
            parse::Value::Or(v) if v.is_empty() => Value::BitFlags(Vec::new()),
            parse::Value::Or(c) => Value::BitFlags(
                c.iter()
                    .map(|p| {
                        let variant_ty = symbols.resolve_type(p)?;
                        let ty = types.key_type(variant_ty);
                        let (_, variant) = ty.meta.path.split_end().ok_or(
                            ConversionError::PathError(crate::path::PathError::EmptyElem(0))
                                .spanned(p.span),
                        )?;

                        Ok::<_, Spanned<ConversionError>>(variant.to_owned().spanned(p.span))
                    })
                    .try_collect()?,
            ),
            parse::Value::Struct {
                name: Some(_),
                fields,
            } => Value::Struct(FieldsKind::Named(
                fields
                    .iter()
                    .map(|(ident, value)| {
                        Ok::<_, Spanned<ConversionError>>((
                            ident.clone(),
                            convert_copy_value(value, symbols, add_value, object_name)?,
                        ))
                    })
                    .try_collect()?,
            )),
            parse::Value::Tuple {
                name: Some(_),
                fields,
            } => Value::Struct(FieldsKind::Unnamed(
                fields
                    .iter()
                    .map(|value| convert_copy_value(value, symbols, add_value, object_name))
                    .try_collect()?,
            )),
            parse::Value::Path(_) => Value::Struct(FieldsKind::Unit),
            parse::Value::Struct { name: None, .. } => todo!(),
            parse::Value::Tuple { name: None, fields } => Value::Tuple(
                fields
                    .iter()
                    .map(|value| convert_copy_value(value, symbols, add_value, object_name))
                    .try_collect()?,
            ),
            parse::Value::Map(items) => Value::Map(
                items
                    .iter()
                    .map(|(key, value)| {
                        Ok::<_, Spanned<ConversionError>>((
                            convert_copy_value(key, symbols, add_value, object_name)?,
                            convert_copy_value(value, symbols, add_value, object_name)?,
                        ))
                    })
                    .try_collect()?,
            ),
            parse::Value::Array(objects) => Value::Array(
                objects
                    .iter()
                    .map(|value| convert_copy_value(value, symbols, add_value, object_name))
                    .try_collect()?,
            ),
            parse::Value::Raw(r) => Value::Primitive(PrimitiveValue::Raw(r.clone())),
        };

        Ok(CopyVal::Copy {
            ty: val_type,
            value: inner.spanned(value.value.span),
            attributes: Attributes(attributes).spanned(value.attributes.span),
        })
    }
}

fn convert_from_copy_value<'a, C: AssetContext>(
    copy_value: impl Into<BorrowCopyVal<'a>>,
    symbols: &Symbols<C>,
    add_value: &mut impl FnMut(TypePathElem<&str>, Val) -> Value,
    expected_type: TypeId,
    object_name: TypePathElem<&str>,
) -> Result<Val> {
    let types = symbols.ctx.type_registry();
    match copy_value.into() {
        BorrowCopyVal::Copy {
            ty: val_ty,
            value,
            attributes,
        } => {
            if let Some(ty) = val_ty
                && !types.can_infer_from(expected_type, ty.value)
            {
                return Err(ConversionError::ExpectedExactType(expected_type).spanned(ty.span));
            }
            let ty_id = if types.key_type(expected_type).kind.instanciable() {
                expected_type
            } else {
                val_ty.as_ref().map(|t| t.value).unwrap_or(expected_type)
            };

            let ty = types.key_type(expected_type);

            let span = value.span;
            let attribute_span = attributes.span;

            macro_rules! parse_unnamed {
                ($fields:expr, $values:expr $(,)?) => {{
                    let fields = $fields;
                    let values = $values;

                    let mut types = fields
                        .required
                        .iter()
                        .map(|ty| (true, ty.id))
                        .chain(fields.optional.iter().map(|ty| (false, ty.id)))
                        .chain(
                            fields
                                .allow_additional
                                .iter()
                                .flat_map(|additional| std::iter::repeat((false, additional.id))),
                        );

                    let mut seq = Vec::with_capacity(values.len());

                    for value in values {
                        let (_, ty) = types.next().ok_or_else(|| {
                            // input tuple too long.
                            ConversionError::ExpectedExactType(ty_id).spanned(value.span())
                        })?;

                        seq.push(convert_from_copy_value(
                            value,
                            symbols,
                            add_value,
                            ty,
                            object_name,
                        )?);
                    }

                    seq
                }};
            }

            macro_rules! parse_named {
                ($named_fields:expr, $fields:expr, $object_name:expr, $skip_unexpected:literal $(,)?) => {{
                    let named_fields = $named_fields;
                    let fields = $fields;
                    let object_name = $object_name;

                    for (field, _) in named_fields.required.iter() {
                        if !fields.contains_key(field.as_str()) {
                            return Err(
                                ConversionError::ExpectedExactType(ty_id).spanned(value.span)
                            );
                        }
                    }
                    let mut new_fields = Fields::with_capacity(fields.len());
                    for (field, value) in fields {
                        let ty = named_fields.get(field.as_str());
                        let ty = match ty {
                            Some(ty) => ty,
                            None if true => continue,
                            None => {
                                return Err(
                                    ConversionError::ExpectedExactType(ty_id).spanned(value.span())
                                );
                            }
                        };
                        new_fields.insert(
                            field.clone(),
                            convert_from_copy_value(value, symbols, add_value, ty.id, object_name)?,
                        );
                    }
                    new_fields
                }};
            }

            let (attributes, leftover_attributes) = {
                let object_name =
                    TypePathElem::new(format!("{object_name}#")).expect("No :: were added");
                let new_attributes = parse_named!(
                    &ty.meta.attributes,
                    &attributes.0,
                    object_name.borrow(),
                    true
                );

                let leftovers = attributes
                    .0
                    .iter()
                    .filter(|(ident, _)| !new_attributes.contains_key(ident.as_str()))
                    .map(|(ident, value)| (ident.clone(), value.clone()))
                    .collect();

                (
                    Attributes(new_attributes),
                    Attributes(leftovers).spanned(attributes.span),
                )
            };

            let mut used_leftover_attributes = false;

            let value = match &ty.kind {
                types::TypeKind::Tuple(fields) => {
                    if let Value::Tuple(values) = &value.value {
                        Ok(Value::Tuple(parse_unnamed!(fields, values)))
                    } else {
                        Err(ConversionError::ExpectedExactType(ty_id).spanned(value.span))
                    }
                }
                types::TypeKind::Array(array_type) => {
                    if let Value::Array(arr) = &value.value {
                        let mut seq = Vec::with_capacity(arr.len());

                        for value in arr {
                            seq.push(convert_from_copy_value(
                                value,
                                symbols,
                                add_value,
                                array_type.ty.id,
                                object_name,
                            )?);
                        }

                        Ok(Value::Array(seq))
                    } else {
                        Err(ConversionError::ExpectedExactType(ty_id).spanned(value.span))
                    }
                }
                types::TypeKind::Map(map_type) => {
                    if let Value::Map(map) = &value.value {
                        let mut seq = Vec::with_capacity(map.len());

                        for (key, value) in map {
                            seq.push((
                                convert_from_copy_value(
                                    key,
                                    symbols,
                                    add_value,
                                    map_type.key.id,
                                    object_name,
                                )?,
                                convert_from_copy_value(
                                    value,
                                    symbols,
                                    add_value,
                                    map_type.value.id,
                                    object_name,
                                )?,
                            ));
                        }

                        Ok(Value::Map(seq))
                    } else {
                        Err(ConversionError::ExpectedExactType(ty_id).spanned(value.span))
                    }
                }
                types::TypeKind::EnumVariant { fields, .. } | types::TypeKind::Struct(fields) => {
                    match fields {
                        types::Fields::Unit => Ok(Value::Struct(FieldsKind::Unit)),
                        types::Fields::Unnamed(unnamed_fields) => {
                            if let Value::Struct(FieldsKind::Unnamed(fields)) = &value.value {
                                Ok(Value::Struct(FieldsKind::Unnamed(parse_unnamed!(
                                    unnamed_fields,
                                    fields,
                                ))))
                            } else {
                                // Expected tuple fields
                                Err(ConversionError::ExpectedExactType(ty_id).spanned(value.span))
                            }
                        }
                        types::Fields::Named(named_fields) => {
                            if let Value::Struct(FieldsKind::Named(fields)) = &value.value {
                                Ok(Value::Struct(FieldsKind::Named(parse_named!(
                                    named_fields,
                                    fields,
                                    object_name,
                                    false,
                                ))))
                            } else {
                                // Expected tuple fields
                                Err(ConversionError::ExpectedExactType(ty_id).spanned(value.span))
                            }
                        }
                    }
                }
                types::TypeKind::Enum { variants, .. } => {
                    used_leftover_attributes = true;
                    variants
                        .iter()
                        .find_map(|(variant, variant_ty)| {
                            let variant_val = convert_from_copy_value(
                                BorrowCopyVal::Copy {
                                    ty: val_ty,
                                    value,
                                    attributes: &leftover_attributes,
                                },
                                symbols,
                                add_value,
                                variant_ty,
                                object_name,
                            )
                            .ok()?;

                            Some(Value::Enum(
                                variant.to_owned().spanned(value.span),
                                Box::new(variant_val),
                            ))
                        })
                        .ok_or(ConversionError::ExpectedExactType(ty_id).spanned(value.span))
                }
                types::TypeKind::BitFlags(variants) => match &value.value {
                    Value::BitFlags(values) => {
                        for value in values {
                            if !variants.variants.contains(value) {
                                return Err(
                                    ConversionError::ExpectedExactType(ty_id).spanned(value.span)
                                );
                            }
                        }

                        Ok(Value::BitFlags(values.clone()))
                    }
                    _ => Err(ConversionError::ExpectedExactType(ty_id).spanned(value.span)),
                },
                types::TypeKind::Primitive(_) => {
                    // We know this value is correct because we checked the type.
                    if let Value::Primitive(prim) = &value.value {
                        Ok(Value::Primitive(prim.clone()))
                    } else {
                        Err(ConversionError::ExpectedExactType(ty_id).spanned(value.span))
                    }
                }
                types::TypeKind::Ref(ty) => {
                    if let Value::Ref(ty) = &value.value {
                        Ok(Value::Ref(ty.clone()))
                    } else {
                        let object_name =
                            TypePathElem::new(format!("{object_name}&{}", ty.inner()))
                                .expect("This should be valid.");

                        used_leftover_attributes = true;
                        let val = convert_from_copy_value(
                            BorrowCopyVal::Copy {
                                ty: val_ty,
                                value,
                                attributes: &leftover_attributes,
                            },
                            symbols,
                            add_value,
                            *ty,
                            object_name.borrow(),
                        )?;

                        let ref_value = add_value(object_name.borrow(), val);

                        Ok(ref_value)
                    }
                }
                types::TypeKind::Transparent(type_id) => {
                    used_leftover_attributes = true;
                    let inner = convert_from_copy_value(
                        BorrowCopyVal::Copy {
                            ty: val_ty,
                            value,
                            attributes: &leftover_attributes,
                        },
                        symbols,
                        add_value,
                        *type_id,
                        object_name,
                    )?;

                    Ok(Value::Transparent(Box::new(inner)))
                }
                // Couldn't resolve type
                types::TypeKind::Trait(_) | types::TypeKind::Generic(_) => {
                    Err(ConversionError::ExpectedExactType(ty_id).spanned(value.span))
                }
            }?;

            if !used_leftover_attributes && !leftover_attributes.0.is_empty() {
                // Unexpected attributes
                return Err(ConversionError::ExpectedExactType(ty_id).spanned(attribute_span));
            }

            Ok(Val {
                ty: expected_type,
                value: value.spanned(span),
                attributes: attributes.spanned(attribute_span),
            })
        }
        BorrowCopyVal::Resolved(val) => {
            if types.can_infer_from(expected_type, val.ty) {
                Ok(val.clone())
            } else {
                // Got wrong type in copy.
                Err(ConversionError::ExpectedExactType(expected_type).spanned(val.value.span))
            }
        }
    }
}

fn set_attributes<C: AssetContext>(
    mut val: Val,
    attributes: &Spanned<parse::Attributes>,
    symbols: &Symbols<C>,
    add_value: &mut impl FnMut(TypePathElem<&str>, Val) -> Value,
    object_name: TypePathElem<&str>,
) -> Result<Val> {
    let types = symbols.ctx.type_registry();
    let ty = types.key_type(val.ty);

    for (ident, value) in attributes.0.iter() {
        let Some(ty) = ty.meta.attributes.get(ident.as_str()) else {
            return Err(ConversionError::UnexpectedIdent.spanned(ident.span));
        };

        let value = convert_value(value, symbols, add_value, ty.id, object_name)?;

        val.attributes.0.insert(ident.clone(), value);
    }

    Ok(val)
}

fn convert_value<'a, C: AssetContext>(
    value: impl Into<BorrowedObject<'a>>,
    symbols: &Symbols<C>,
    add_value: &mut impl FnMut(TypePathElem<&str>, Val) -> Value,
    expected_type: TypeId,
    object_name: TypePathElem<&str>,
) -> Result<Val> {
    let value: BorrowedObject<'a> = value.into();

    // Convert from copy values, and add any attributes the ref had.
    if let parse::Value::Ref(r) = &value.value.value
        && let Some(ident) = r.as_ident()
        && let Some((_, Some(val))) = symbols.try_resolve_copy(ident)
    {
        let res = convert_from_copy_value(val, symbols, add_value, expected_type, object_name)?;

        return if !value.attributes.0.is_empty() {
            set_attributes(res, value.attributes, symbols, add_value, object_name)
        } else {
            Ok(res)
        };
    }

    let types = symbols.ctx.type_registry();
    let val_type = value_type(value, symbols)?;

    let ty_id = {
        if let Some(val_type) = val_type.as_ref() {
            if !types.can_infer_from(expected_type, val_type.value) {
                return Err(
                    ConversionError::ExpectedExactType(expected_type).spanned(value.value.span)
                );
            }
        }

        // If `expected_type` isn't instantiable, i.e is a trait, we go off of the value type.
        if !types.key_type(expected_type).kind.instanciable() {
            val_type.unwrap_or(expected_type.spanned(value.value.span))
        } else {
            expected_type.spanned(val_type.map(|s| s.span).unwrap_or(value.value.span))
        }
    };

    let ty = types.key_type(ty_id.value);

    macro_rules! parse_unnamed {
        ($fields:expr, $value:expr $(,)?) => {{
            let fields = $fields;
            let value = $value;

            if let parse::Value::Tuple { fields: values, .. } = &value.value.value {
                let mut types = fields
                    .required
                    .iter()
                    .map(|ty| (true, ty.id))
                    .chain(fields.optional.iter().map(|ty| (false, ty.id)))
                    .chain(
                        fields
                            .allow_additional
                            .iter()
                            .flat_map(|additional| std::iter::repeat((false, additional.id))),
                    );

                let mut new_values = Vec::new();

                for value in values {
                    let (_, ty) = types.next().ok_or_else(|| {
                        // input tuple too long
                        ConversionError::expected_ty(ty_id.clone())
                    })?;

                    new_values.push(convert_value(value, symbols, add_value, ty, object_name)?)
                }

                if let Some((true, _ty)) = types.next() {
                    // input tuple too short
                    return Err(ConversionError::expected_ty(ty_id));
                }

                Ok(new_values)
            } else {
                // Expected unnamed fields
                Err(ConversionError::expected_ty(ty_id))
            }
        }};
    }

    macro_rules! parse_named {
        ($named_fields:expr, $fields:expr, $object_name:expr, $skip_unexpected:literal $(,)?) => {{
            let named_fields = $named_fields;
            let fields = $fields;
            let object_name = $object_name;

            for (field, _) in named_fields.required.iter() {
                if !fields.contains_key(field.as_str()) {
                    // Missing required field.
                    return Err(ConversionError::expected_ty(ty_id));
                }
            }
            let mut new_fields = Fields::with_capacity(fields.len());
            for (field, value) in fields {
                let ty = named_fields.get(field.as_str());

                let ty = match ty {
                    Some(ty) => ty,
                    None if $skip_unexpected => continue,
                    None => {
                        return Err(ConversionError::expected_ty(ty_id));
                    }
                };

                new_fields.insert(
                    field.clone(),
                    convert_value(value, symbols, add_value, ty.id, object_name)?,
                );
            }

            new_fields
        }};
    }

    let (attributes, leftover_attributes) = {
        let object_name = TypePathElem::new(format!("{object_name}#")).expect("No :: were added");
        let attributes = parse_named!(
            &ty.meta.attributes,
            &value.attributes.0,
            object_name.borrow(),
            true,
        );

        let leftovers = value
            .attributes
            .0
            .iter()
            .filter(|(ident, _)| !attributes.contains_key(ident.as_str()))
            .map(|(ident, value)| (ident.clone(), value.clone()))
            .collect();

        (
            Attributes(attributes),
            parse::Attributes(leftovers).spanned(value.attributes.span),
        )
    };

    let mut used_leftover_attributes = false;

    // TODO: Improve errors.
    let val = match &ty.kind {
        types::TypeKind::Tuple(tuple) => {
            if matches!(
                &value.value.value,
                parse::Value::Tuple { name: Some(_), .. }
            ) {
                // Expected unnamed tuple
                return Err(ConversionError::expected_ty(ty_id));
            }

            parse_unnamed!(tuple, value).map(Value::Tuple)
        }
        types::TypeKind::Array(array_type) => {
            if let parse::Value::Array(arr) = &value.value.value {
                if array_type
                    .len
                    .is_some_and(|expected_len| expected_len != arr.len())
                {
                    // input array not the right length
                    return Err(ConversionError::expected_ty(ty_id));
                }

                let mut values = Vec::with_capacity(arr.len());

                for value in arr {
                    values.push(convert_value(
                        value,
                        symbols,
                        add_value,
                        array_type.ty.id,
                        object_name,
                    )?);
                }

                Ok(Value::Array(values))
            } else {
                Err(ConversionError::expected_ty(ty_id))
            }
        }
        types::TypeKind::Map(map_type) => {
            if let parse::Value::Map(map) = &value.value.value {
                if map_type
                    .len
                    .is_some_and(|expected_len| expected_len != map.len())
                {
                    // input map not the right length
                    return Err(ConversionError::expected_ty(ty_id));
                }

                let mut values = Vec::with_capacity(map.len());

                for (key, value) in map {
                    values.push((
                        convert_value(key, symbols, add_value, map_type.key.id, object_name)?,
                        convert_value(value, symbols, add_value, map_type.value.id, object_name)?,
                    ));
                }

                Ok(Value::Map(values))
            } else {
                Err(ConversionError::expected_ty(ty_id))
            }
        }
        types::TypeKind::EnumVariant { fields, .. } | types::TypeKind::Struct(fields) => {
            match fields {
                types::Fields::Unit => Ok(Value::Struct(FieldsKind::Unit)),
                types::Fields::Unnamed(tuple_type) => {
                    if matches!(&value.value.value, parse::Value::Tuple { name: None, .. }) {
                        // Expected named tuple
                        return Err(ConversionError::expected_ty(ty_id));
                    }

                    Ok(Value::Struct(FieldsKind::Unnamed(parse_unnamed!(
                        tuple_type, value,
                    )?)))
                }
                types::Fields::Named(named_fields) => {
                    if let parse::Value::Struct {
                        name: Some(_),
                        fields,
                    } = &value.value.value
                    {
                        Ok(Value::Struct(FieldsKind::Named(parse_named!(
                            named_fields,
                            fields,
                            object_name,
                            false,
                        ))))
                    } else {
                        Err(ConversionError::expected_ty(ty_id))
                    }
                }
            }
        }
        types::TypeKind::Enum { variants, .. } => {
            if let Some(val_type) = val_type.as_ref() {
                let variant = if let types::TypeKind::EnumVariant {
                    variant, enum_type, ..
                } = &types.key_type(val_type.value).kind
                {
                    debug_assert_eq!(*enum_type, ty_id.value);
                    debug_assert_eq!(variants.get(variant.borrow()), Some(val_type.value));
                    Some((variant.borrow(), *val_type))
                } else {
                    // First see if we have this exact type as a flattened type, then see if we can infer to any type.
                    variants
                        .iter()
                        .find(|(_, ty)| *ty == val_type.value)
                        .or_else(|| {
                            variants
                                .iter()
                                .find(|(_, ty)| types.can_infer_from(*ty, val_type.value))
                        })
                        .map(|(v, t)| (v, t.spanned(value.value.span)))
                };

                if let Some((variant, variant_ty)) = variant {
                    used_leftover_attributes = true;
                    let variant_val = convert_value(
                        BorrowedObject {
                            value: value.value,
                            attributes: &leftover_attributes,
                        },
                        symbols,
                        add_value,
                        variant_ty.value,
                        object_name,
                    )?;

                    Ok(Value::Enum(
                        variant.to_owned().spanned(variant_ty.span),
                        Box::new(variant_val),
                    ))
                } else {
                    Err(ConversionError::expected_ty(ty_id))
                }
            } else {
                // If we don't know the value type, we can look through all the enum's types and see if any
                // successfully get converted.
                used_leftover_attributes = true;
                variants
                    .iter()
                    .find_map(|(variant, variant_ty)| {
                        let variant_val = convert_value(
                            BorrowedObject {
                                value: value.value,
                                attributes: &leftover_attributes,
                            },
                            symbols,
                            add_value,
                            variant_ty,
                            object_name,
                        )
                        .ok()?;

                        Some(Value::Enum(
                            variant.to_owned().spanned(variant_val.value.span),
                            Box::new(variant_val),
                        ))
                    })
                    .ok_or(ConversionError::expected_ty(ty_id))
            }
        }
        types::TypeKind::BitFlags(variants) => match &value.value.value {
            parse::Value::Path(path) => {
                if let Some(val_type) = val_type.as_ref()
                    && let types::TypeKind::EnumVariant {
                        variant,
                        enum_type,
                        fields,
                    } = &types.key_type(val_type.value).kind
                {
                    debug_assert!(matches!(fields, types::Fields::Unit));
                    debug_assert_eq!(*enum_type, ty_id.value);
                    debug_assert!(variants.variants.contains(variant));

                    Ok(Value::BitFlags(vec![variant.clone().spanned(path.span)]))
                } else {
                    Err(ConversionError::expected_ty(ty_id))
                }
            }
            parse::Value::Or(paths) => {
                if paths.is_empty() {
                    Ok(Value::BitFlags(Vec::new()))
                } else {
                    let mut variants = Vec::with_capacity(paths.len());

                    for path in paths {
                        let ty = symbols.resolve_type(path)?;

                        let types::TypeKind::EnumVariant {
                            variant,
                            enum_type,
                            fields: types::Fields::Unit,
                        } = &types.key_type(ty).kind
                        else {
                            // Wrong type for path
                            return Err(ConversionError::expected_ty(ty_id));
                        };

                        if *enum_type != ty_id.value {
                            return Err(ConversionError::expected_ty(ty_id));
                        }

                        variants.push(variant.clone().spanned(path.span))
                    }

                    Ok(Value::BitFlags(variants))
                }
            }
            _ => Err(ConversionError::expected_ty(ty_id)),
        },
        types::TypeKind::Ref(ty) => {
            if let parse::Value::Ref(asset) = &value.value.value {
                let (_, path) = symbols.resolve_asset(asset)?;

                Ok(Value::Ref(path))
            } else {
                let object_name = TypePathElem::new(format!("{object_name}&{}", ty.inner()))
                    .expect("We didn't add any ::");
                used_leftover_attributes = true;
                let val = convert_value(
                    BorrowedObject {
                        value: value.value,
                        attributes: &leftover_attributes,
                    },
                    symbols,
                    add_value,
                    *ty,
                    object_name.borrow(),
                )?;

                let ref_value = add_value(object_name.borrow(), val);

                Ok(ref_value)
            }
        }
        types::TypeKind::Primitive(primitive) => match primitive {
            types::Primitive::Any => Err(ConversionError::ExpectedType.spanned(value.value.span)),
            types::Primitive::Num => {
                if let parse::Value::Num(n) = &value.value.value {
                    Ok(Value::Primitive(PrimitiveValue::Num(*n)))
                } else {
                    Err(ConversionError::expected_ty(ty_id))
                }
            }
            types::Primitive::Str => {
                if let parse::Value::Str(s) = &value.value.value {
                    Ok(Value::Primitive(PrimitiveValue::Str(s.clone())))
                } else {
                    Err(ConversionError::expected_ty(ty_id))
                }
            }
            types::Primitive::Bool => {
                if let parse::Value::Bool(b) = &value.value.value {
                    Ok(Value::Primitive(PrimitiveValue::Bool(*b)))
                } else {
                    Err(ConversionError::expected_ty(ty_id))
                }
            }
            types::Primitive::Unit => Ok(Value::Primitive(PrimitiveValue::Unit)),
            types::Primitive::Raw => {
                if let parse::Value::Raw(s) = &value.value.value {
                    Ok(Value::Primitive(PrimitiveValue::Raw(s.clone())))
                } else {
                    Err(ConversionError::expected_ty(ty_id))
                }
            }
        },
        types::TypeKind::Transparent(type_id) => {
            used_leftover_attributes = true;
            Ok(Value::Transparent(Box::new(convert_value(
                BorrowedObject {
                    value: value.value,
                    attributes: &leftover_attributes,
                },
                symbols,
                add_value,
                *type_id,
                object_name,
            )?)))
        }
        types::TypeKind::Trait(_) | types::TypeKind::Generic(_) => {
            Err(ConversionError::ExpectedType.spanned(value.value.span))
        }
    }?;

    if !used_leftover_attributes && !leftover_attributes.0.is_empty() {
        // Unexpected attributes
        return Err(ConversionError::expected_ty(ty_id));
    }

    Ok(Val {
        value: val.spanned(value.value.span),
        attributes: attributes.spanned(value.attributes.span),
        ty: *ty_id,
    })
}

/// Converts a parsed value to a object value. With a conversion context and existing symbols. Also does some rudementory checking if the symbols are okay.
fn convert_object<C: AssetContext>(
    path: TypePath<&str>,
    name: TypePathElem<&str>,
    value: &ParseObject,
    symbols: &Symbols<C>,
    expected_type: TypeId,
    add_value: &mut impl FnMut(TypePathElem<&str>, Val) -> Value,
) -> Result<Object> {
    let value = convert_value(value, symbols, add_value, expected_type, name)?;

    Ok(create_object(path, name, value))
}

fn create_object(path: TypePath<&str>, name: TypePathElem<&str>, value: Val) -> Object {
    Object {
        object_path: path.combine(&name),
        value,
    }
}
