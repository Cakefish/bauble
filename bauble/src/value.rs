use std::{
    borrow::Cow,
    collections::{HashMap, HashSet},
};

use indexmap::IndexMap;
use rust_decimal::Decimal;

use crate::{
    BaubleContext, BaubleError, BaubleErrors, FileId, VariantKind,
    context::PathReference,
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

#[derive(Clone, Debug)]
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

impl<T> Value<T> {
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

#[derive(Debug)]
pub struct Object {
    pub object_path: TypePath,
    pub value: Val,
}

#[derive(Clone, Debug)]
pub enum ConversionError {
    UnregisteredAsset,
    UnresolvedType,
    AmbiguousUse {
        ident: TypePathElem,
    },
    ExpectedBitfield {
        got: TypeId,
    },
    WrongTupleLength {
        got: usize,
        tuple_ty: TypeId,
    },
    MissingField {
        attribute: bool,
        field: String,
        ty: TypeId,
    },
    UnexpectedField {
        attribute: bool,
        field: Ident,
        ty: TypeId,
    },
    DuplicateAttribute {
        first: Ident,
        second: Ident,
    },
    WrongFieldKind(TypeId),
    UnknownVariant {
        variant: Spanned<TypePathElem>,
        ty: TypeId,
    },
    RefError(Box<RefError>),
    ExpectedExactType {
        expected: TypeId,
        got: Option<TypeId>,
    },
    PathError(crate::path::PathError),
    CopyCycle(Vec<(Spanned<String>, Vec<Spanned<String>>)>),
    ErrorInCopy {
        copy: Spanned<TypePathElem>,
        error: Box<Spanned<ConversionError>>,
    },
}

#[derive(Clone, Copy, Debug)]
pub enum RefKind {
    Module,
    Asset,
    Type,
    Any,
}

#[derive(Clone, Debug)]
enum PathKind {
    Direct(TypePath),
    /// TypePath::*::TypePathElem
    Indirect(TypePath, TypePathElem),
}

impl TryFrom<&Path> for PathKind {
    type Error = Spanned<crate::path::PathError>;

    fn try_from(value: &Path) -> std::result::Result<Self, Self::Error> {
        let mut leading =
            TypePath::new(value.leading.join("::")).map_err(|e| e.spanned(value.span()))?;

        match &value.last.value {
            PathEnd::WithIdent(ident) => Ok(PathKind::Indirect(
                leading,
                TypePathElem::new(ident.as_str())
                    .map_err(|e| e.spanned(ident.span))?
                    .to_owned(),
            )),
            PathEnd::Ident(ident) => {
                leading
                    .push_str(ident.as_str())
                    .map_err(|e| e.spanned(ident.span))?;
                Ok(PathKind::Direct(leading))
            }
        }
    }
}

#[derive(Clone, Debug)]
pub struct RefError {
    uses: Option<HashMap<TypePathElem, RefCopy>>,
    path: PathKind,
    path_ref: PathReference,
    kind: RefKind,
}

impl From<crate::path::PathError> for ConversionError {
    fn from(value: crate::path::PathError) -> Self {
        Self::PathError(value)
    }
}

impl BaubleError for Spanned<ConversionError> {
    fn msg_general(&self, ctx: &BaubleContext) -> crate::error::ErrorMsg {
        let types = ctx.type_registry();
        let msg = match &self.value {
            ConversionError::CopyCycle(_) => Cow::Borrowed("A copy cycle was found"),
            ConversionError::PathError(_) => Cow::Borrowed("Path error"),
            ConversionError::AmbiguousUse { .. } => Cow::Borrowed("Ambiguous use"),
            ConversionError::ExpectedBitfield { .. } => Cow::Borrowed("Expected bitfield"),
            ConversionError::UnresolvedType => Cow::Borrowed("Unresolved type"),
            ConversionError::WrongTupleLength { tuple_ty, .. } => Cow::Owned(format!(
                "Wrong amount of fields for `{}`",
                types.key_type(*tuple_ty).meta.path
            )),
            ConversionError::MissingField { ty, attribute, .. } => Cow::Owned(format!(
                "Missing {} for `{}`",
                if *attribute { "attribute" } else { "field" },
                types.key_type(*ty).meta.path
            )),
            ConversionError::UnexpectedField { ty, attribute, .. } => Cow::Owned(format!(
                "Unexpected {} for `{}`",
                if *attribute { "attribute" } else { "field" },
                types.key_type(*ty).meta.path
            )),
            ConversionError::DuplicateAttribute { .. } => Cow::Borrowed("Duplicate attribute"),
            ConversionError::WrongFieldKind(ty) => Cow::Owned(format!(
                "Wrong kind of fields for `{}`",
                types.key_type(*ty).meta.path
            )),
            ConversionError::UnknownVariant { ty, .. } => Cow::Owned(format!(
                "Unknown variant for `{}`",
                types.key_type(*ty).meta.path
            )),
            ConversionError::RefError(ref_err) => Cow::Borrowed(match ref_err.kind {
                RefKind::Module => "Failed to resolve module",
                RefKind::Asset => "Failed to resolve asset",
                RefKind::Type => "Failed to resolve type",
                RefKind::Any => "Failed to resolve path",
            }),
            ConversionError::ExpectedExactType { expected, .. } => Cow::Owned(format!(
                "Expected the type `{}`",
                types.key_type(*expected).meta.path
            )),
            ConversionError::ErrorInCopy { error, .. } => return error.msg_general(ctx),
            ConversionError::UnregisteredAsset => Cow::Borrowed("Unregistered asset"),
        };

        msg.spanned(self.span)
    }

    fn msgs_specific(
        &self,
        ctx: &BaubleContext,
    ) -> Vec<(crate::error::ErrorMsg, crate::error::Level)> {
        fn describe_fields(_types: &types::TypeRegistry, fields: &types::Fields) -> &'static str {
            match fields {
                types::Fields::Unit => "no fields",
                types::Fields::Unnamed(_) => "unnamed fields",
                types::Fields::Named(_) => "named fields",
            }
        }
        fn describe_type(types: &types::TypeRegistry, id: TypeId) -> String {
            match &types.key_type(id).kind {
                types::TypeKind::Tuple(_) => "A tuple".to_string(),
                types::TypeKind::Array(array_type) => format!(
                    "an array with the item `{}`, which is {}",
                    types.key_type(array_type.ty.id).meta.path,
                    describe_type(types, array_type.ty.id),
                ),
                types::TypeKind::Map(map_type) => format!(
                    "a map with the key `{}`, which is {}, and the value `{}`, which is {}",
                    types.key_type(map_type.key.id).meta.path,
                    describe_type(types, map_type.key.id),
                    types.key_type(map_type.value.id).meta.path,
                    describe_type(types, map_type.value.id),
                ),
                types::TypeKind::Struct(fields) => {
                    format!("a struct with {}", describe_fields(types, fields))
                }
                types::TypeKind::Enum { .. } => "an enum".to_string(),
                types::TypeKind::BitFlags(_) => "a bitflag type".to_string(),
                types::TypeKind::Ref(id) => format!(
                    "a reference to `{}`, which is {}",
                    types.key_type(*id).meta.path,
                    describe_type(types, *id)
                ),
                types::TypeKind::Primitive(primitive) => match primitive {
                    types::Primitive::Any => "any type",
                    types::Primitive::Num => "a number",
                    types::Primitive::Str => "a string",
                    types::Primitive::Bool => "a bool",
                    types::Primitive::Unit => "a unit value",
                    types::Primitive::Raw => "a raw value",
                }
                .to_string(),
                types::TypeKind::Transparent(id) => format!(
                    "a transparent type over `{}`, which is {}",
                    types.key_type(*id).meta.path,
                    describe_type(types, *id)
                ),
                types::TypeKind::EnumVariant { fields, .. } => {
                    format!("an enum variant with {}", describe_fields(types, fields))
                }
                types::TypeKind::Trait(_) => "a trait".to_string(),
                types::TypeKind::Generic(set) => {
                    let s = types
                        .iter_type_set(set)
                        .next()
                        .map(|t| {
                            let s = describe_type(types, t);

                            s.split_once(' ').map(|(_, s)| s.to_string()).unwrap_or(s)
                        })
                        .unwrap_or("type".to_string());

                    format!("a generic {s}")
                }
            }
        }

        fn get_suggestions<S: std::borrow::Borrow<str> + Clone + std::fmt::Display>(
            options: impl IntoIterator<Item = S>,
            input: &str,
        ) -> Option<String> {
            const MAX_EDIT_DISTANCE: usize = 3;
            let mut options = options
                .into_iter()
                .map(|s| (edit_distance::edit_distance(s.borrow(), input), s))
                .collect::<Vec<_>>();
            options.sort_by_key(|(d, _)| *d);

            let mut suggestions = options
                .iter()
                .filter(|(distance, ident)| *distance <= 2 || ident.borrow().contains(input))
                .map(|f| f.1.clone())
                .collect::<Vec<_>>();
            if suggestions.is_empty()
                && let Some(closest) = options
                    .iter()
                    .min_by_key(|(d, _)| *d)
                    .filter(|(d, _)| *d <= MAX_EDIT_DISTANCE)
            {
                suggestions.push(closest.1.clone());
            }
            match suggestions
                .into_iter()
                .map(|s| format!("`{s}`"))
                .collect::<Vec<_>>()
                .as_slice()
            {
                [] => None,
                [option] => Some(format!("Did you mean {option}?")),
                [options @ .., option] => Some(format!(
                    "Did you mean any of {} or {option}?",
                    // Show at most 5 suggestions.
                    options[..options.len().min(5)].join(", ")
                )),
            }
        }

        let types = ctx.type_registry();

        let msg: Cow<'_, str> = match &self.value {
            ConversionError::UnresolvedType => Cow::Borrowed(
                "This top level value needs to either have it's type denoted, or be a value that can be resolved to a specific type",
            ),
            ConversionError::PathError(err) => {
                let generic = match err {
                    crate::path::PathError::EmptyElem(_) => "Malformed path",
                    crate::path::PathError::MissingDelimiterEnd(_) => "Malformed path",
                    crate::path::PathError::MissingDelimiterStart(_) => "Malformed path",
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
                    crate::path::PathError::MissingDelimiterEnd(i) => {
                        errors.push((
                            Cow::Borrowed("This delimiter is missing a closing delimiter")
                                .spanned(span_index(*i)),
                            Level::Error,
                        ));
                    }
                    crate::path::PathError::MissingDelimiterStart(i) => {
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
            ConversionError::AmbiguousUse { ident } => Cow::Owned(format!(
                "The identifier `{ident}` has been imported multiple times"
            )),
            ConversionError::ExpectedBitfield { got } => Cow::Owned(format!(
                "But got the type `{}` which is {}",
                types.key_type(*got).meta.path,
                describe_type(types, *got)
            )),
            ConversionError::WrongTupleLength { got, tuple_ty } => {
                if let types::TypeKind::Tuple(fields)
                | types::TypeKind::Struct(types::Fields::Unnamed(fields))
                | types::TypeKind::EnumVariant {
                    fields: types::Fields::Unnamed(fields),
                    ..
                } = &types.key_type(*tuple_ty).kind
                {
                    let min_fields = fields.required.len();
                    let max_fields = if fields.allow_additional.is_none() {
                        Some(min_fields + fields.optional.len())
                    } else {
                        None
                    };

                    let expected = match max_fields {
                        Some(max_fields) if max_fields == min_fields => {
                            format!(
                                "{min_fields} item{}",
                                if min_fields == 1 { "" } else { "s" }
                            )
                        }
                        Some(max_fields) => {
                            format!("at least {min_fields} and at most {max_fields} items")
                        }
                        None => format!(
                            "at least {min_fields} item{}",
                            if min_fields == 1 { "" } else { "s" }
                        ),
                    };

                    Cow::Owned(format!("Expected {expected} but got {got}"))
                } else {
                    Cow::Owned(format!("Got {got}"))
                }
            }
            ConversionError::MissingField {
                attribute, field, ..
            } => Cow::Owned(format!(
                "Missing the `{}` {field}",
                if *attribute { "attribute" } else { "field" }
            )),
            ConversionError::UnexpectedField {
                attribute,
                field,
                ty,
            } => {
                let ty = types.key_type(*ty);

                let fields = if *attribute {
                    Some(&ty.meta.attributes)
                } else if let types::TypeKind::Struct(types::Fields::Named(fields))
                | types::TypeKind::EnumVariant {
                    fields: types::Fields::Named(fields),
                    ..
                } = &ty.kind
                {
                    Some(fields)
                } else {
                    None
                };

                let mut errs = vec![(
                    Spanned::new(
                        field.span,
                        Cow::Owned(format!(
                            "Unexpected {} `{field}`",
                            if *attribute { "attribute" } else { "field" },
                        )),
                    ),
                    Level::Error,
                )];

                if let Some(fields) = fields
                    && let Some(suggestions) = get_suggestions(
                        fields
                            .required
                            .iter()
                            .chain(&fields.optional)
                            .map(|(s, _)| s.as_str()),
                        field.as_str(),
                    )
                {
                    errs.push((
                        Spanned::new(field.span, Cow::Owned(suggestions)),
                        Level::Info,
                    ));
                }

                return errs;
            }
            ConversionError::DuplicateAttribute { first, second } => {
                return vec![
                    (
                        Spanned::new(
                            second.span,
                            Cow::Owned(format!("Duplicate attribute `{second}`")),
                        ),
                        Level::Error,
                    ),
                    (
                        Spanned::new(first.span, Cow::Borrowed("First used here")),
                        Level::Info,
                    ),
                ];
            }
            ConversionError::WrongFieldKind(ty) => {
                if let types::TypeKind::Struct(fields)
                | types::TypeKind::EnumVariant { fields, .. } = &types.key_type(*ty).kind
                {
                    Cow::Owned(format!("Expected {}", describe_fields(types, fields)))
                } else {
                    Cow::Borrowed("Wrong fields")
                }
            }
            ConversionError::UnknownVariant { variant, ty } => {
                let ty = types.key_type(*ty);
                let suggestions = match &ty.kind {
                    types::TypeKind::Enum { variants } => {
                        get_suggestions(variants.iter().map(|s| s.0.into_inner()), variant.as_str())
                    }
                    types::TypeKind::BitFlags(variants) => get_suggestions(
                        variants.variants.iter().map(|s| s.as_str()),
                        variant.as_str(),
                    ),
                    _ => None,
                };

                let mut errs = vec![(
                    Spanned::new(
                        variant.span,
                        Cow::Owned(format!("Unexpected variant `{variant}`")),
                    ),
                    Level::Error,
                )];

                if let Some(suggestions) = suggestions {
                    errs.push((
                        Spanned::new(variant.span, Cow::Owned(suggestions)),
                        Level::Info,
                    ));
                }

                return errs;
            }
            ConversionError::RefError(ref_err) => {
                let inner = match (
                    &ref_err.path_ref.module,
                    &ref_err.path_ref.asset,
                    &ref_err.path_ref.ty,
                ) {
                    (None, None, None) => "",
                    (None, None, Some(_)) => ", but it refers to a type",
                    (None, Some(_), None) => ", but it refers to an asset",
                    (None, Some(_), Some(_)) => ", but it refers to an asset and a type",
                    (Some(_), None, None) => ", but it refers to a module",
                    (Some(_), None, Some(_)) => ", but it refers to a module and a type",
                    (Some(_), Some(_), None) => ", but it refers to a module and an asset",
                    (Some(_), Some(_), Some(_)) => "",
                };
                let mut errs = vec![(
                    Spanned::new(
                        self.span,
                        Cow::Owned(format!(
                            "Expected this path to refer to {}{inner}",
                            match ref_err.kind {
                                RefKind::Module => "a module",
                                RefKind::Asset => "an asset",
                                RefKind::Type => "a type",
                                RefKind::Any => "a valid reference",
                            }
                        )),
                    ),
                    Level::Error,
                )];
                match &ref_err.path {
                    PathKind::Direct(path) => {
                        let options = ctx
                            .ref_kinds(TypePath::empty(), ref_err.kind, None)
                            .map(|p| p.into_inner());
                        if path.len() == 1
                            && let Some(uses) = &ref_err.uses
                        {
                            if let Some(suggestions) = get_suggestions(
                                uses.iter()
                                    .filter(|(_, p)| match p {
                                        RefCopy::Unresolved => false,
                                        RefCopy::Resolved(_) => false,
                                        RefCopy::Ref(path_reference) => {
                                            path_reference.asset.is_some()
                                        }
                                    })
                                    .map(|(ident, _)| ident.as_str())
                                    .chain(options),
                                path.as_str(),
                            ) {
                                errs.push((
                                    Spanned::new(self.span, Cow::Owned(suggestions)),
                                    Level::Info,
                                ));
                            }
                        } else if let Some(suggestions) = get_suggestions(options, path.as_str()) {
                            errs.push((
                                Spanned::new(self.span, Cow::Owned(suggestions)),
                                Level::Info,
                            ));
                        }
                    }
                    PathKind::Indirect(module, ident) => {
                        if let Some(suggestions) = get_suggestions(
                            ctx.ref_kinds(module.borrow(), ref_err.kind, None)
                                .filter_map(|s| {
                                    s.split_end()
                                        .map(|(_, ident)| format!("{module}::*::{ident}"))
                                }),
                            &format!("{module}::*::{ident}"),
                        ) {
                            errs.push((
                                Spanned::new(self.span, Cow::Owned(suggestions)),
                                Level::Info,
                            ));
                        }
                    }
                }

                return errs;
            }
            ConversionError::ExpectedExactType { expected, got } => {
                let s = if let Some(got) = got {
                    format!(
                        "Expected `{}` which is {}, but got `{}` which is {}",
                        types.key_type(*expected).meta.path,
                        describe_type(types, *expected),
                        types.key_type(*got).meta.path,
                        describe_type(types, *got),
                    )
                } else {
                    format!(
                        "Expected `{}` which is {}, but couldn't resolve type",
                        types.key_type(*expected).meta.path,
                        describe_type(types, *expected),
                    )
                };

                Cow::Owned(s)
            }
            ConversionError::ErrorInCopy { copy, error } => {
                let mut v = error.msgs_specific(ctx);

                v.push((
                    Spanned::new(copy.span, Cow::Borrowed("In this copy value")),
                    Level::Info,
                ));
                v.push((
                    Spanned::new(self.span, Cow::Borrowed("In this copy reference")),
                    Level::Info,
                ));

                return v;
            }
            ConversionError::UnregisteredAsset => Cow::Borrowed(
                "This asset hasn't been registered with `BaubleContext::register_asset`",
            ),
        };

        vec![(msg.spanned(self.span), Level::Error)]
    }

    fn help(&self, ctx: &BaubleContext) -> Option<Cow<'static, str>> {
        if let ConversionError::RefError(ref_err) = &self.value
            && ref_err.uses.is_some()
            && let PathKind::Direct(ident) = &ref_err.path
            && ident.len() == 1
        {
            let suggestions = ctx
                .ref_kinds(TypePath::empty(), ref_err.kind, None)
                .filter(|path| path.ends_with(ident.borrow()))
                .map(|path| format!("`{path}`"))
                .collect::<Vec<_>>();

            return Some(Cow::Owned(match suggestions.as_slice() {
                [] => return None,
                [option] => format!("Maybe you meant to use {option}?"),
                [rest @ .., option] => format!(
                    "Maybe you meant to use one of {} or {option}?",
                    rest.join(", ")
                ),
            }));
        }

        None
    }
}

type Result<T> = std::result::Result<T, Spanned<ConversionError>>;

impl From<Spanned<crate::path::PathError>> for Spanned<ConversionError> {
    fn from(value: Spanned<crate::path::PathError>) -> Self {
        value.map(ConversionError::PathError)
    }
}

#[derive(Clone, Debug)]
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

    fn add(self, other: PathReference) -> Option<Self> {
        match self {
            RefCopy::Unresolved | RefCopy::Resolved(_) => None,
            RefCopy::Ref(reference) => Some(RefCopy::Ref(reference.combined(other)?)),
        }
    }
}

#[derive(Clone)]
pub(crate) struct Symbols<'a> {
    ctx: &'a BaubleContext,
    uses: HashMap<TypePathElem, RefCopy>,
}

impl<'a> Symbols<'a> {
    pub fn new(ctx: &'a BaubleContext) -> Self {
        Self {
            ctx,
            uses: HashMap::default(),
        }
    }

    fn add_ref(
        &mut self,
        ident: TypePathElem,
        reference: PathReference,
    ) -> std::result::Result<(), ConversionError> {
        let r = self.uses.entry(ident.clone()).or_default();

        *r = r
            .clone()
            .add(reference)
            .ok_or(ConversionError::AmbiguousUse { ident })?;

        Ok(())
    }

    fn add(&mut self, symbols: Symbols) {
        self.uses.extend(symbols.uses)
    }

    fn add_use(&mut self, use_: &Use) -> Result<()> {
        fn add_use_inner(
            this: &mut Symbols,
            leading: TypePath,
            end: &Spanned<PathTreeEnd>,
        ) -> Result<()> {
            match &end.value {
                PathTreeEnd::Group(g) => {
                    for node in g {
                        let mut leading = leading.clone();
                        for s in &node.leading.value {
                            leading.push_str(&s.value).map_err(|e| e.spanned(s.span))?;
                            if this.ctx.get_ref(leading.borrow()).is_none() {
                                return Err(ConversionError::RefError(Box::new(RefError {
                                    uses: None,
                                    path: PathKind::Direct(leading),
                                    path_ref: PathReference::empty(),
                                    kind: RefKind::Module,
                                }))
                                .spanned(s.span));
                            }
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
                        return Err(ConversionError::RefError(Box::new(RefError {
                            uses: None,
                            path: PathKind::Direct(leading),
                            path_ref: PathReference::empty(),
                            kind: RefKind::Module,
                        }))
                        .spanned(end.span));
                    }
                }
                PathTreeEnd::PathEnd(PathEnd::Ident(ident)) => {
                    let path_end =
                        TypePathElem::new(ident.as_str()).map_err(|e| e.spanned(ident.span))?;
                    let path = leading.join(&path_end);
                    if let Some(reference) = this.ctx.get_ref(path.borrow()) {
                        this.add_ref(path_end.to_owned(), reference)
                            .map_err(|e| e.spanned(ident.span))?;
                    } else {
                        return Err(ConversionError::RefError(Box::new(RefError {
                            uses: None,
                            path: PathKind::Direct(path),
                            path_ref: PathReference::empty(),
                            kind: RefKind::Any,
                        }))
                        .spanned(end.span));
                    }
                }
                PathTreeEnd::PathEnd(PathEnd::WithIdent(ident)) => {
                    let path_end =
                        TypePathElem::new(ident.as_str()).map_err(|e| e.spanned(ident.span))?;
                    if let Some(reference) = this.ctx.ref_with_ident(leading.borrow(), path_end) {
                        this.add_ref(path_end.to_owned(), reference)
                            .map_err(|e| e.spanned(ident.span))?;
                    } else {
                        return Err(ConversionError::RefError(Box::new(RefError {
                            uses: None,
                            path: PathKind::Indirect(leading, path_end.to_owned()),
                            path_ref: PathReference::empty(),
                            kind: RefKind::Any,
                        }))
                        .spanned(end.span));
                    }
                }
            }
            Ok(())
        }

        let mut leading = TypePath::empty();
        for l in use_.leading.iter() {
            leading.push_str(l).map_err(|e| e.spanned(l.span))?;
            if self.ctx.get_ref(leading.borrow()).is_none() {
                return Err(ConversionError::RefError(Box::new(RefError {
                    uses: None,
                    path: PathKind::Direct(leading),
                    path_ref: PathReference::empty(),
                    kind: RefKind::Module,
                }))
                .spanned(l.span));
            }
        }
        add_use_inner(self, leading, &use_.end)
    }

    fn try_resolve_copy<'b>(
        &'b self,
        ident: &str,
    ) -> Option<(TypePathElem<&'b str>, Option<&'b CopyVal>)> {
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

    fn resolve_item(&self, raw_path: &Path, ref_kind: RefKind) -> Result<Cow<PathReference>> {
        let mut leading = TypePath::empty();
        let mut path_iter = raw_path.leading.iter();
        if let Some(first) = path_iter.next() {
            leading = self.get_module(first.as_str()).unwrap_or(
                TypePath::new(first.as_str())
                    .map_err(|e| e.spanned(first.span))?
                    .to_owned(),
            );

            if self.ctx.get_ref(leading.borrow()).is_none() {
                return Err(ConversionError::RefError(Box::new(RefError {
                    uses: None,
                    path: PathKind::Direct(leading),
                    path_ref: PathReference::empty(),
                    kind: RefKind::Module,
                }))
                .spanned(first.span));
            }

            for ident in path_iter {
                leading
                    .push_str(ident.as_str())
                    .map_err(|e| e.spanned(ident.span))?;

                if self.ctx.get_ref(leading.borrow()).is_none() {
                    return Err(ConversionError::RefError(Box::new(RefError {
                        uses: None,
                        path: PathKind::Direct(leading),
                        path_ref: PathReference::empty(),
                        kind: RefKind::Module,
                    }))
                    .spanned(ident.span));
                }
            }
        } else if let PathEnd::Ident(ident) = &raw_path.last.value
            && let Some(RefCopy::Ref(r)) = self.uses.get(ident.as_str())
        {
            return Ok(Cow::Borrowed(r));
        }
        match &raw_path.last.value {
            PathEnd::WithIdent(ident) => {
                let ident = TypePathElem::new(ident.as_str()).map_err(|e| e.spanned(ident.span))?;
                self.ctx
                    .ref_with_ident(leading.borrow(), ident)
                    .ok_or_else(|| {
                        ConversionError::RefError(Box::new(RefError {
                            uses: Some(self.uses.clone()),
                            path: PathKind::Indirect(leading, ident.to_owned()),
                            path_ref: PathReference::empty(),
                            kind: ref_kind,
                        }))
                        .spanned(raw_path.span())
                    })
            }
            PathEnd::Ident(ident) => {
                let span = ident.span;
                let ident = TypePathElem::new(ident.as_str()).map_err(|e| e.spanned(ident.span))?;
                let path = leading.join(&ident);
                self.ctx.get_ref(path.borrow()).ok_or_else(|| {
                    if let Some(r) = self.ctx.get_ref(leading.borrow())
                        && let Some(ty) = r.ty
                        && matches!(
                            self.ctx.type_registry().key_type(ty).kind,
                            types::TypeKind::Enum { .. } | types::TypeKind::BitFlags(_)
                        )
                    {
                        return ConversionError::UnknownVariant {
                            variant: ident.to_owned().spanned(span),
                            ty,
                        }
                        .spanned(raw_path.span());
                    }
                    ConversionError::RefError(Box::new(RefError {
                        uses: Some(self.uses.clone()),
                        path: PathKind::Direct(path),
                        path_ref: PathReference::empty(),
                        kind: ref_kind,
                    }))
                    .spanned(raw_path.span())
                })
            }
        }
        .map(Cow::Owned)
    }

    fn resolve_asset(&self, path: &Spanned<Path>) -> Result<(TypeId, TypePath)> {
        let item = self.resolve_item(path, RefKind::Asset)?;

        item.asset.clone().ok_or(
            ConversionError::RefError(Box::new(RefError {
                uses: Some(self.uses.clone()),
                path: PathKind::try_from(&path.value)?,
                path_ref: item.into_owned(),
                kind: RefKind::Asset,
            }))
            .spanned(path.span),
        )
    }

    fn resolve_type(&self, path: &Spanned<Path>) -> Result<TypeId> {
        let item = self.resolve_item(path, RefKind::Type)?;

        item.ty.ok_or(
            ConversionError::RefError(Box::new(RefError {
                uses: Some(self.uses.clone()),
                path: PathKind::try_from(&path.value)?,
                path_ref: item.into_owned(),
                kind: RefKind::Type,
            }))
            .spanned(path.span),
        )
    }
}

pub fn register_assets(
    path: TypePath<&str>,
    ctx: &mut crate::context::BaubleContext,
    default_uses: impl IntoIterator<Item = (TypePathElem, PathReference)>,
    values: &Values,
) -> std::result::Result<(), Vec<Spanned<ConversionError>>> {
    let mut uses = default_uses
        .into_iter()
        .map(|(key, val)| (key, RefCopy::Ref(val)))
        .collect();
    let mut errors = Vec::new();

    let mut symbols = Symbols { ctx: &*ctx, uses };
    for use_ in &values.uses {
        if let Err(e) = symbols.add_use(use_) {
            errors.push(e);
        }
    }

    Symbols { uses, .. } = symbols;

    // TODO: Register these in a correct order to allow for assets referencing assets.
    for (ident, binding) in &values.values {
        let ident = &TypePathElem::new(ident.as_str()).expect("Invariant");
        let path = path.join(ident);
        let mut symbols = Symbols { ctx: &*ctx, uses };

        let ty = if let Some(ty) = &binding.type_path {
            symbols.resolve_type(ty)
        } else {
            value_type(&binding.object, &symbols)
                .map(|v| {
                    default_value_type(&symbols, binding.object.value.value.primitive_type(), v)
                })
                .transpose()
                .unwrap_or(Err(
                    ConversionError::UnresolvedType.spanned(binding.object.value.span)
                ))
                .and_then(|v| {
                    if ctx.type_registry().key_type(v).kind.instanciable() {
                        Ok(v)
                    } else {
                        Err(ConversionError::UnresolvedType.spanned(binding.object.value.span))
                    }
                })
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
                ctx.register_asset(path.borrow(), ty);
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

pub(crate) fn convert_values(
    file: FileId,
    values: Values,
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

        Value::Ref(path.join(&name))
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

fn find_copy_refs<'a>(
    object: &ParseObject,
    symbols: &'a Symbols,
    found: &mut impl FnMut(Spanned<TypePathElem<&'a str>>),
) {
    for obj in object.attributes.0.values() {
        find_copy_refs(obj, symbols, found)
    }

    match &object.value.value {
        parse::Value::Ref(reference) => {
            if let Some(ident) = reference.as_ident() {
                if let Some((ident, _)) = symbols.try_resolve_copy(&ident) {
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

fn default_value_type(
    symbols: &Symbols,
    primitive: Option<types::Primitive>,
    value_type: Option<Spanned<TypeId>>,
) -> Option<TypeId> {
    let types = symbols.ctx.type_registry();
    if let Some(value_type) = value_type {
        let enum_type = match &types.key_type(value_type.value).kind {
            types::TypeKind::EnumVariant { enum_type, .. } => *enum_type,
            types::TypeKind::Generic(set) => {
                if let Some(t) = types.iter_type_set(set).next()
                    && let types::TypeKind::EnumVariant { enum_type, .. } = &types.key_type(t).kind
                {
                    types
                        .key_type(*enum_type)
                        .meta
                        .generic_base_type
                        .expect("Invariant, if the EnumVariant is generic so is the enum type")
                        .into()
                } else {
                    return Some(value_type.value);
                }
            }
            _ => return Some(value_type.value),
        };

        Some(enum_type)
    } else {
        primitive.map(|primitive| types.primitive_type(primitive))
    }
}

fn value_type<'a>(
    value: impl Into<BorrowedObject<'a>>,
    symbols: &Symbols,
) -> Result<Option<Spanned<TypeId>>> {
    let value: BorrowedObject<'a> = value.into();
    let types = symbols.ctx.type_registry();
    let ty = match &value.value.value {
        parse::Value::Unit => None,
        parse::Value::Num(_) => None,
        parse::Value::Bool(_) => None,
        parse::Value::Str(_) => None,
        parse::Value::Ref(path) => {
            if let Some(ident) = path.as_ident()
                && let Some((_, Some(copy))) = symbols.try_resolve_copy(&ident)
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
                                return Err(ConversionError::ExpectedBitfield { got: *enum_type }
                                    .spanned(path.span));
                            }

                            if let Some(generic) = enum_ty.meta.generic_base_type {
                                Ok(generic.into())
                            } else {
                                panic!(
                                    "If the variant has a generic type, the bitfield should too"
                                );
                            }
                        } else {
                            // Generic type doesn't have any instances. Or the instance we got wasn't a bitfield.
                            Err(ConversionError::ExpectedBitfield { got: variant_ty }
                                .spanned(path.span))
                        }
                    }
                    _ => {
                        Err(ConversionError::ExpectedBitfield { got: variant_ty }
                            .spanned(path.span))
                    }
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
                            return Err(ConversionError::ExpectedExactType {
                                expected: *ty,
                                got: Some(enum_type),
                            }
                            .spanned(path.span));
                        }
                    }
                    None => ty = Some(enum_type),
                }
            }

            ty.map(|t| t.spanned(value.value.span))
        }
        parse::Value::Raw(_) => None,
    };

    Ok(ty)
}

fn set_attributes(
    mut val: Val,
    attributes: &Spanned<parse::Attributes>,
    symbols: &Symbols,
    add_value: &mut impl FnMut(TypePathElem<&str>, Val) -> Value,
    object_name: TypePathElem<&str>,
) -> Result<Val> {
    let types = symbols.ctx.type_registry();
    let ty = types.key_type(val.ty);

    for (ident, value) in attributes.0.iter() {
        let Some(ty) = ty.meta.attributes.get(ident.as_str()) else {
            return Err(ConversionError::UnexpectedField {
                attribute: true,
                field: ident.clone(),
                ty: val.ty,
            }
            .spanned(ident.span));
        };

        if let Some((first, _)) = value.attributes.0.get_key_value(ident.as_str()) {
            return Err(ConversionError::DuplicateAttribute {
                first: first.clone(),
                second: ident.clone(),
            }
            .spanned(ident.span));
        }

        let value = convert_value(value, symbols, add_value, ty.id, object_name)?;

        val.attributes.0.insert(ident.clone(), value);
    }

    Ok(val)
}

fn convert_copy_value<'a>(
    value: impl Into<BorrowedObject<'a>>,
    symbols: &Symbols,
    add_value: &mut impl FnMut(TypePathElem<&str>, Val) -> Value,
    object_name: TypePathElem<&str>,
) -> Result<CopyVal> {
    let value: BorrowedObject<'a> = value.into();
    let types = symbols.ctx.type_registry();
    let val_type = value_type(value, symbols)?;

    if let Some(val_type) = val_type.as_ref()
        && types.key_type(val_type.value).kind.instanciable()
    {
        let val_type = default_value_type(symbols, value.value.primitive_type(), Some(*val_type))
            .unwrap_or(val_type.value);
        convert_value(value, symbols, add_value, val_type, object_name).map(CopyVal::Resolved)
    } else {
        let mut parse_attributes = || {
            value
                .attributes
                .0
                .iter()
                .map(|(ident, value)| {
                    Ok::<_, Spanned<ConversionError>>((
                        ident.clone(),
                        convert_copy_value(value, symbols, add_value, object_name)?,
                    ))
                })
                .try_collect::<IndexMap<_, _>>()
        };

        // Resolve copy references.
        if let parse::Value::Ref(r) = &value.value.value
            && let Some(ident) = r.as_ident()
            && let Some((copy, Some(val))) = symbols.try_resolve_copy(ident.value)
        {
            return match val {
                CopyVal::Copy {
                    ty,
                    value,
                    attributes,
                } => {
                    let mut attributes = attributes.clone();
                    for (attribute, value) in parse_attributes()? {
                        if let Some((first, _)) = attributes.0.get_key_value(attribute.as_str()) {
                            return Err(ConversionError::DuplicateAttribute {
                                first: first.clone(),
                                second: attribute.clone(),
                            }
                            .spanned(attribute.span));
                        }

                        attributes.0.insert(attribute, value);
                    }

                    Ok(CopyVal::Copy {
                        ty: *ty,
                        value: value.clone(),
                        attributes,
                    })
                }
                CopyVal::Resolved(val) => Ok(CopyVal::Resolved(
                    set_attributes(
                        val.clone(),
                        value.attributes,
                        symbols,
                        add_value,
                        object_name,
                    )
                    .map_err(|err| {
                        ConversionError::ErrorInCopy {
                            copy: copy.to_owned().spanned(val.span()),
                            error: Box::new(err),
                        }
                        .spanned(value.value.span)
                    })?,
                )),
            };
        }

        let attributes = parse_attributes()?;
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
                        let (_, variant) = ty.meta.path.get_end().ok_or(
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

fn convert_from_copy<'a>(
    copy_value: impl Into<BorrowCopyVal<'a>>,
    symbols: &Symbols,
    add_value: &mut impl FnMut(TypePathElem<&str>, Val) -> Value,
    expected_type: TypeId,
    object_name: TypePathElem<&str>,
) -> Result<Val> {
    convert_from_copy_with_attributes(
        copy_value,
        symbols,
        add_value,
        expected_type,
        object_name,
        None,
    )
}

fn convert_from_copy_with_attributes<'a>(
    copy_value: impl Into<BorrowCopyVal<'a>>,
    symbols: &Symbols,
    add_value: &mut impl FnMut(TypePathElem<&str>, Val) -> Value,
    expected_type: TypeId,
    object_name: TypePathElem<&str>,
    extra_attributes: Option<&Spanned<parse::Attributes>>,
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
                return Err(ConversionError::ExpectedExactType {
                    expected: expected_type,
                    got: Some(ty.value),
                }
                .spanned(ty.span));
            }
            let ty_id = if types.key_type(expected_type).kind.instanciable() {
                expected_type
            } else {
                default_value_type(symbols, value.primitive_type(), *val_ty)
                    .unwrap_or(expected_type)
            };

            let ty = types.key_type(expected_type);

            let span = value.span;
            let attribute_span = attributes.span;

            macro_rules! parse_unnamed_copy {
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

                    let l = values.len();
                    for value in values {
                        let (_, ty) = types.next().ok_or_else(|| {
                            // input tuple too long.
                            ConversionError::WrongTupleLength {
                                got: l,
                                tuple_ty: ty_id,
                            }
                            .spanned(value.span())
                        })?;

                        seq.push(convert_from_copy(
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

            macro_rules! parse_named_copy {
                ($named_fields:expr, $fields:expr, $object_name:expr, $attribute:literal $(,)?) => {{
                    let named_fields = $named_fields;
                    let fields = $fields;
                    let object_name = $object_name;

                    for (field, _) in named_fields.required.iter() {
                        if !fields.contains_key(field.as_str()) {
                            return Err(ConversionError::MissingField {
                                attribute: $attribute,
                                ty: ty_id,
                                field: field.to_string(),
                            }
                            .spanned(value.span));
                        }
                    }
                    let mut new_fields = Fields::with_capacity(fields.len());
                    for (field, value) in fields {
                        let ty = named_fields.get(field.as_str());
                        let ty = match ty {
                            Some(ty) => ty,
                            None if $attribute => continue,
                            None => {
                                return Err(ConversionError::UnexpectedField {
                                    attribute: $attribute,
                                    ty: ty_id,
                                    field: field.clone(),
                                }
                                .spanned(value.span()));
                            }
                        };
                        new_fields.insert(
                            field.clone(),
                            convert_from_copy(value, symbols, add_value, ty.id, object_name)?,
                        );
                    }
                    new_fields
                }};
            }

            let (attributes, leftover_attributes) = {
                let object_name =
                    TypePathElem::new(format!("{object_name}#")).expect("No :: were added");

                let mut leftovers = Fields::new();

                let mut new_attributes = Fields::with_capacity(attributes.0.len());
                if let Some(extra) = extra_attributes {
                    for (field, value) in &extra.0 {
                        let ty = match ty.meta.attributes.get(field.as_str()) {
                            Some(ty) => ty,
                            None => {
                                leftovers.insert(
                                    field.clone(),
                                    convert_copy_value(
                                        value,
                                        symbols,
                                        add_value,
                                        object_name.borrow(),
                                    )?,
                                );
                                continue;
                            }
                        };

                        new_attributes.insert(
                            field.clone(),
                            convert_value(value, symbols, add_value, ty.id, object_name.borrow())?,
                        );
                    }
                }
                for (field, value) in &attributes.0 {
                    let ty = match (
                        ty.meta.attributes.get(field.as_str()),
                        new_attributes.contains_key(field.as_str()),
                    ) {
                        (Some(ty), false) => ty,
                        _ => {
                            if let Some((first, _)) = leftovers.get_key_value(field.as_str()) {
                                return Err(ConversionError::DuplicateAttribute {
                                    first: first.clone(),
                                    second: field.clone(),
                                }
                                .spanned(field.span));
                            }
                            leftovers.insert(field.clone(), value.clone());

                            continue;
                        }
                    };
                    // We checked that `new_attributes` didn't contain this field.
                    new_attributes.insert(
                        field.clone(),
                        convert_from_copy(value, symbols, add_value, ty.id, object_name.borrow())?,
                    );
                }

                for (attr, _) in ty.meta.attributes.required.iter() {
                    if !new_attributes.contains_key(attr.as_str()) {
                        return Err(ConversionError::MissingField {
                            attribute: true,
                            field: attr.clone(),
                            ty: ty_id,
                        }
                        .spanned(attribute_span));
                    }
                }

                (
                    Attributes(new_attributes),
                    Attributes(leftovers).spanned(attributes.span),
                )
            };

            let mut used_leftover_attributes = false;

            let expected_err = || {
                ConversionError::ExpectedExactType {
                    expected: expected_type,
                    got: val_ty.as_deref().copied(),
                }
                .spanned(value.span)
            };

            let value = match &ty.kind {
                types::TypeKind::Tuple(fields) => {
                    if let Value::Tuple(values) = &value.value {
                        Ok(Value::Tuple(parse_unnamed_copy!(fields, values)))
                    } else {
                        Err(expected_err())
                    }
                }
                types::TypeKind::Array(array_type) => {
                    if let Value::Array(arr) = &value.value {
                        let mut seq = Vec::with_capacity(arr.len());

                        for value in arr {
                            seq.push(convert_from_copy(
                                value,
                                symbols,
                                add_value,
                                array_type.ty.id,
                                object_name,
                            )?);
                        }

                        Ok(Value::Array(seq))
                    } else {
                        Err(expected_err())
                    }
                }
                types::TypeKind::Map(map_type) => {
                    if let Value::Map(map) = &value.value {
                        let mut seq = Vec::with_capacity(map.len());

                        for (key, value) in map {
                            seq.push((
                                convert_from_copy(
                                    key,
                                    symbols,
                                    add_value,
                                    map_type.key.id,
                                    object_name,
                                )?,
                                convert_from_copy(
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
                        Err(expected_err())
                    }
                }
                types::TypeKind::EnumVariant { fields, .. } | types::TypeKind::Struct(fields) => {
                    match fields {
                        types::Fields::Unit => Ok(Value::Struct(FieldsKind::Unit)),
                        types::Fields::Unnamed(unnamed_fields) => {
                            if let Value::Struct(FieldsKind::Unnamed(fields)) = &value.value {
                                Ok(Value::Struct(FieldsKind::Unnamed(parse_unnamed_copy!(
                                    unnamed_fields,
                                    fields,
                                ))))
                            } else {
                                // Expected unnamed fields
                                Err(ConversionError::WrongFieldKind(ty_id).spanned(value.span))
                            }
                        }
                        types::Fields::Named(named_fields) => {
                            if let Value::Struct(FieldsKind::Named(fields)) = &value.value {
                                Ok(Value::Struct(FieldsKind::Named(parse_named_copy!(
                                    named_fields,
                                    fields,
                                    object_name,
                                    false,
                                ))))
                            } else {
                                // Expected unnamed fields
                                Err(ConversionError::WrongFieldKind(ty_id).spanned(value.span))
                            }
                        }
                    }
                }
                types::TypeKind::Enum { variants, .. } => {
                    used_leftover_attributes = true;
                    if let Some((variant, variant_ty)) = variants.iter().find(|(_, variant_ty)| {
                        val_ty.is_some_and(|t| {
                            t.value == *variant_ty
                                || types
                                    .key_type(*variant_ty)
                                    .meta
                                    .generic_base_type
                                    .is_some_and(|gt| t.value == gt.into())
                        })
                    }) {
                        let variant_val = convert_from_copy(
                            BorrowCopyVal::Copy {
                                ty: val_ty,
                                value,
                                attributes: &leftover_attributes,
                            },
                            symbols,
                            add_value,
                            variant_ty,
                            object_name,
                        )?;

                        Ok(Value::Enum(
                            variant.to_owned().spanned(value.span),
                            Box::new(variant_val),
                        ))
                    } else {
                        variants
                            .iter()
                            .find_map(|(variant, variant_ty)| {
                                let variant_val = convert_from_copy(
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
                            .ok_or(expected_err())
                    }
                }
                types::TypeKind::BitFlags(variants) => match &value.value {
                    Value::BitFlags(values) => {
                        for value in values {
                            if !variants.variants.contains(value) {
                                return Err(ConversionError::UnknownVariant {
                                    variant: value.clone(),
                                    ty: ty_id,
                                }
                                .spanned(value.span));
                            }
                        }

                        Ok(Value::BitFlags(values.clone()))
                    }
                    _ => Err(expected_err()),
                },
                types::TypeKind::Primitive(_) => {
                    // We know this value is correct because we checked the type.
                    if let Value::Primitive(prim) = &value.value {
                        Ok(Value::Primitive(prim.clone()))
                    } else {
                        Err(expected_err())
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
                        let val = convert_from_copy(
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
                    let inner = convert_from_copy(
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
                types::TypeKind::Trait(_) | types::TypeKind::Generic(_) => Err(expected_err()),
            }?;

            if !used_leftover_attributes
                && let Some((ident, _)) = leftover_attributes.value.0.into_iter().next()
            {
                // Unexpected attributes
                return Err(ConversionError::UnexpectedField {
                    attribute: true,
                    field: ident,
                    ty: ty_id,
                }
                .spanned(attribute_span));
            }

            Ok(Val {
                ty: expected_type,
                value: value.spanned(span),
                attributes: attributes.spanned(attribute_span),
            })
        }
        BorrowCopyVal::Resolved(val) => {
            if types.can_infer_from(expected_type, val.ty) {
                let mut val = val.clone();
                if let Some(extra) = extra_attributes {
                    val = set_attributes(val, extra, symbols, add_value, object_name)?;
                }
                Ok(val)
            } else {
                // Got wrong type in copy.
                Err(ConversionError::ExpectedExactType {
                    expected: expected_type,
                    got: Some(val.ty),
                }
                .spanned(val.value.span))
            }
        }
    }
}

fn convert_value<'a>(
    value: impl Into<BorrowedObject<'a>>,
    symbols: &Symbols,
    add_value: &mut impl FnMut(TypePathElem<&str>, Val) -> Value,
    expected_type: TypeId,
    object_name: TypePathElem<&str>,
) -> Result<Val> {
    let value: BorrowedObject<'a> = value.into();

    // Convert from copy values, and add any attributes the ref had.
    if let parse::Value::Ref(r) = &value.value.value
        && let Some(ident) = r.as_ident()
        && let Some((copy, Some(val))) = symbols.try_resolve_copy(ident.value)
    {
        return convert_from_copy_with_attributes(
            val,
            symbols,
            add_value,
            expected_type,
            object_name,
            Some(value.attributes),
        )
        .map_err(|err| {
            ConversionError::ErrorInCopy {
                copy: copy.to_owned().spanned(val.span()),
                error: Box::new(err),
            }
            .spanned(value.value.span)
        });
    }

    let types = symbols.ctx.type_registry();
    let val_type = value_type(value, symbols)?;

    let ty_id = {
        if let Some(val_type) = val_type.as_ref() {
            if !types.can_infer_from(expected_type, val_type.value) {
                return Err(ConversionError::ExpectedExactType {
                    expected: expected_type,
                    got: Some(val_type.value),
                }
                .spanned(value.value.span));
            }
        }

        // If `expected_type` isn't instantiable, i.e is a trait, we go off of the value type.
        if !types.key_type(expected_type).kind.instanciable() {
            default_value_type(symbols, value.value.primitive_type(), val_type)
                .unwrap_or(expected_type)
                .spanned(val_type.map_or(value.value.span, |s| s.span))
        } else {
            expected_type.spanned(val_type.map(|s| s.span).unwrap_or(value.value.span))
        }
    };

    let ty = types.key_type(ty_id.value);

    let expected_err = || {
        ConversionError::ExpectedExactType {
            expected: expected_type,
            got: val_type.map(|s| s.value),
        }
        .spanned(ty_id.span)
    };

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
                        expected_err()
                    })?;

                    new_values.push(convert_value(value, symbols, add_value, ty, object_name)?)
                }

                if let Some((true, _ty)) = types.next() {
                    // input tuple too short
                    return Err(expected_err());
                }

                Ok(new_values)
            } else {
                // Expected unnamed fields
                Err(expected_err())
            }
        }};
    }

    macro_rules! parse_named {
        ($named_fields:expr, $fields:expr, $object_name:expr, $is_attribute:literal $(,)?) => {{
            let named_fields = $named_fields;
            let fields = $fields;
            let object_name = $object_name;

            for (field, _) in named_fields.required.iter() {
                if !fields.contains_key(field.as_str()) {
                    // Missing required field.
                    return Err(ConversionError::MissingField {
                        attribute: $is_attribute,
                        field: field.clone(),
                        ty: ty_id.value,
                    }
                    .spanned(value.value.span));
                }
            }
            let mut new_fields = Fields::with_capacity(fields.len());
            for (field, value) in fields {
                let ty = named_fields.get(field.as_str());

                let ty = match ty {
                    Some(ty) => ty,
                    None if $is_attribute => continue,
                    None => {
                        return Err(ConversionError::UnexpectedField {
                            attribute: $is_attribute,
                            field: field.clone(),
                            ty: ty_id.value,
                        }
                        .spanned(value.value.span));
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

    let val = match &ty.kind {
        types::TypeKind::Tuple(tuple) => {
            if matches!(
                &value.value.value,
                parse::Value::Tuple { name: Some(_), .. }
            ) {
                // Expected unnamed tuple
                return Err(expected_err());
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
                    return Err(expected_err());
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
                Err(expected_err())
            }
        }
        types::TypeKind::Map(map_type) => {
            if let parse::Value::Map(map) = &value.value.value {
                if map_type
                    .len
                    .is_some_and(|expected_len| expected_len != map.len())
                {
                    // input map not the right length
                    return Err(expected_err());
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
                Err(expected_err())
            }
        }
        types::TypeKind::EnumVariant { fields, .. } | types::TypeKind::Struct(fields) => {
            match fields {
                types::Fields::Unit => Ok(Value::Struct(FieldsKind::Unit)),
                types::Fields::Unnamed(tuple_type) => {
                    if matches!(&value.value.value, parse::Value::Tuple { name: None, .. }) {
                        // Expected named tuple
                        return Err(expected_err());
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
                        Err(expected_err())
                    }
                }
            }
        }
        types::TypeKind::Enum { variants, .. } => {
            if let Some(val_type) = val_type.as_ref() {
                let variant = if let types::TypeKind::EnumVariant {
                    variant, enum_type, ..
                } = &types.key_type(val_type.value).kind
                    && *enum_type == ty_id.value
                {
                    debug_assert_eq!(variants.get(variant.borrow()), Some(val_type.value));
                    Some((variant.borrow(), *val_type))
                } else if types.key_type(ty_id.value).meta.generic_base_type.is_some()
                    && let types::TypeKind::Generic(generic) = &types.key_type(val_type.value).kind
                    && let Some(instance) = types.iter_type_set(generic).next()
                    && let types::TypeKind::EnumVariant { variant, .. } =
                        &types.key_type(instance).kind
                    && types.key_type(instance).meta.generic_base_type
                        == types.key_type(ty_id.value).meta.generic_base_type
                {
                    Some((
                        variant.borrow(),
                        variants
                            .get(variant.borrow())
                            .expect("This will exist here")
                            .spanned(val_type.span),
                    ))
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
                    Err(expected_err())
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
                    .ok_or(expected_err())
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
                    Err(expected_err())
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
                            return Err(expected_err());
                        };

                        if *enum_type != ty_id.value {
                            return Err(expected_err());
                        }

                        variants.push(variant.clone().spanned(path.span))
                    }

                    Ok(Value::BitFlags(variants))
                }
            }
            _ => Err(expected_err()),
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
            types::Primitive::Any => Err(expected_err()),
            types::Primitive::Num => {
                if let parse::Value::Num(n) = &value.value.value {
                    Ok(Value::Primitive(PrimitiveValue::Num(*n)))
                } else {
                    Err(expected_err())
                }
            }
            types::Primitive::Str => {
                if let parse::Value::Str(s) = &value.value.value {
                    Ok(Value::Primitive(PrimitiveValue::Str(s.clone())))
                } else {
                    Err(expected_err())
                }
            }
            types::Primitive::Bool => {
                if let parse::Value::Bool(b) = &value.value.value {
                    Ok(Value::Primitive(PrimitiveValue::Bool(*b)))
                } else {
                    Err(expected_err())
                }
            }
            types::Primitive::Unit => Ok(Value::Primitive(PrimitiveValue::Unit)),
            types::Primitive::Raw => {
                if let parse::Value::Raw(s) = &value.value.value {
                    Ok(Value::Primitive(PrimitiveValue::Raw(s.clone())))
                } else {
                    Err(expected_err())
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
        types::TypeKind::Trait(_) | types::TypeKind::Generic(_) => Err(expected_err()),
    }?;

    if !used_leftover_attributes
        && let Some((ident, _)) = leftover_attributes.value.0.into_iter().next()
    {
        // Unexpected attributes
        return Err(ConversionError::UnexpectedField {
            attribute: true,
            field: ident,
            ty: *ty_id,
        }
        .spanned(value.attributes.span));
    }

    Ok(Val {
        value: val.spanned(value.value.span),
        attributes: attributes.spanned(value.attributes.span),
        ty: *ty_id,
    })
}

/// Converts a parsed value to a object value. With a conversion context and existing symbols. Also does some rudementory checking if the symbols are okay.
fn convert_object(
    path: TypePath<&str>,
    name: TypePathElem<&str>,
    value: &ParseObject,
    symbols: &Symbols,
    expected_type: TypeId,
    add_value: &mut impl FnMut(TypePathElem<&str>, Val) -> Value,
) -> Result<Object> {
    let value = convert_value(value, symbols, add_value, expected_type, name)?;

    Ok(create_object(path, name, value))
}

fn create_object(path: TypePath<&str>, name: TypePathElem<&str>, value: Val) -> Object {
    Object {
        object_path: path.join(&name),
        value,
    }
}
