use std::{borrow::Cow, collections::HashMap};

use crate::{
    BaubleContext, BaubleError, CustomError,
    context::PathReference,
    error::Level,
    path::{TypePath, TypePathElem},
    spanned::{SpanExt, Spanned},
    types::{self, TypeId},
};

use super::{Ident, PathKind, RefCopy};

#[derive(Clone, Debug)]
pub struct RefError {
    pub(super) uses: Option<HashMap<TypePathElem, RefCopy>>,
    pub(super) path: PathKind,
    pub(super) path_ref: PathReference,
    pub(super) kind: RefKind,
}

impl From<crate::path::PathError> for ConversionError {
    fn from(value: crate::path::PathError) -> Self {
        Self::PathError(value)
    }
}

#[derive(Clone, Debug)]
pub enum ConversionError {
    UnregisteredAsset,
    UnresolvedType,
    MissingRequiredTrait {
        tr: types::TraitId,
        ty: TypeId,
    },
    AmbiguousUse {
        ident: TypePathElem,
    },
    ExpectedBitfield {
        got: TypeId,
    },
    WrongLength {
        got: usize,
        ty: TypeId,
    },
    MissingField {
        attribute: bool,
        field: String,
        ty: TypeId,
    },
    WrongFields {
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
    AttributeOnNull {
        attribute: Ident,
        ty: TypeId,
    },
    WrongFieldKind(TypeId),
    UnknownVariant {
        variant: Spanned<TypePathElem>,
        ty: TypeId,
    },
    VariantErrors {
        variant_errors: Vec<(TypeId, Box<Spanned<ConversionError>>)>,
        ty: TypeId,
    },
    RefError(Box<RefError>),
    NotNullable(TypeId),
    ExpectedExactType {
        expected: TypeId,
        got: Option<TypeId>,
    },
    PathError(crate::path::PathError),
    Cycle(Vec<(Spanned<String>, Vec<Spanned<String>>)>),
    ErrorInCopy {
        copy: Spanned<TypePathElem>,
        error: Box<Spanned<ConversionError>>,
    },
    Custom(CustomError),
}

impl From<CustomError> for ConversionError {
    fn from(value: CustomError) -> Self {
        Self::Custom(value)
    }
}

#[derive(Clone, Copy, Debug)]
pub enum RefKind {
    Module,
    Asset,
    Type,
    Any,
}
impl BaubleError for Spanned<ConversionError> {
    fn msg_general(&self, ctx: &BaubleContext) -> crate::error::ErrorMsg {
        let types = ctx.type_registry();
        let msg = match &self.value {
            ConversionError::MissingRequiredTrait { .. } => Cow::Borrowed("Missing required trait"),
            ConversionError::Cycle(_) => Cow::Borrowed("A cycle was found"),
            ConversionError::PathError(_) => Cow::Borrowed("Path error"),
            ConversionError::AmbiguousUse { .. } => Cow::Borrowed("Ambiguous use"),
            ConversionError::ExpectedBitfield { .. } => Cow::Borrowed("Expected bitfield"),
            ConversionError::UnresolvedType => Cow::Borrowed("Unresolved type"),
            ConversionError::WrongLength { ty, .. } => Cow::Owned(format!(
                "Wrong amount of items for `{}`",
                types.key_type(*ty).meta.path
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
            ConversionError::WrongFields { ty } => Cow::Owned(format!(
                "Wrong type of fields for `{}`",
                types.key_type(*ty).meta.path
            )),
            ConversionError::DuplicateAttribute { .. } => Cow::Borrowed("Duplicate attribute"),
            ConversionError::AttributeOnNull { .. } => {
                Cow::Borrowed("Attributes aren't allowed on null values")
            }
            ConversionError::WrongFieldKind(ty) => Cow::Owned(format!(
                "Wrong kind of fields for `{}`",
                types.key_type(*ty).meta.path
            )),
            ConversionError::UnknownVariant { ty, .. } => Cow::Owned(format!(
                "Unknown variant for `{}`",
                types.key_type(*ty).meta.path
            )),
            ConversionError::VariantErrors { ty, .. } => Cow::Owned(format!(
                "Failed to parse this as the enum `{}`",
                types.key_type(*ty).meta.path
            )),
            ConversionError::RefError(ref_err) => Cow::Borrowed(match ref_err.kind {
                RefKind::Module => "Failed to resolve module",
                RefKind::Asset => "Failed to resolve asset",
                RefKind::Type => "Failed to resolve type",
                RefKind::Any => "Failed to resolve path",
            }),
            ConversionError::NotNullable(ty) => Cow::Owned(format!(
                "The type `{}` is not nullable",
                types.key_type(*ty).meta.path
            )),
            ConversionError::ExpectedExactType { expected, .. } => Cow::Owned(format!(
                "Expected the type `{}`",
                types.key_type(*expected).meta.path
            )),
            ConversionError::ErrorInCopy { error, .. } => return error.msg_general(ctx),
            ConversionError::UnregisteredAsset => Cow::Borrowed("Unregistered asset"),
            ConversionError::Custom(custom) => custom.message.clone(),
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
                types::TypeKind::Or(_) => "a bitflag type".to_string(),
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
            ConversionError::MissingRequiredTrait { tr, ty } => Cow::Owned(format!(
                "The type `{}` doesn't implement the trait `{}`",
                types.key_type(*ty).meta.path,
                types.key_type(*tr).meta.path
            )),
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
            ConversionError::Cycle(cycle) => {
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
            ConversionError::WrongLength { got, ty } => match &types.key_type(*ty).kind {
                types::TypeKind::Tuple(fields)
                | types::TypeKind::Struct(types::Fields::Unnamed(fields))
                | types::TypeKind::EnumVariant {
                    fields: types::Fields::Unnamed(fields),
                    ..
                } => {
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
                }
                types::TypeKind::Array(types::ArrayType { len, .. })
                | types::TypeKind::Map(types::MapType { len, .. }) => Cow::Owned(format!(
                    "Expected {} but got {got}",
                    len.map_or("any".to_string(), |l| l.to_string())
                )),

                _ => Cow::Owned(format!("Got {got}")),
            },
            ConversionError::MissingField {
                attribute, field, ..
            } => Cow::Owned(format!(
                "Missing the {} `{field}`",
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
            ConversionError::WrongFields { ty } => {
                if let types::TypeKind::EnumVariant { fields, .. }
                | types::TypeKind::Struct(fields) = &types.key_type(*ty).kind
                {
                    Cow::Owned(format!(
                        "Expected this to be {} fields",
                        match fields {
                            types::Fields::Unit => "unit",
                            types::Fields::Unnamed(_) => "unnamed",
                            types::Fields::Named(_) => "named",
                        }
                    ))
                } else if matches!(types.key_type(*ty).kind, types::TypeKind::Or(_)) {
                    Cow::Borrowed("Expected this to not have fields")
                } else {
                    Cow::Borrowed("Here")
                }
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
            ConversionError::AttributeOnNull { attribute, ty } => {
                let ty = types.key_type(*ty);
                if ty.meta.attributes.get(attribute).is_some() {
                    Cow::Owned(format!(
                        "The type `{}` has this attribute, but it isn't allowed on `null` values",
                        ty.meta.path
                    ))
                } else {
                    Cow::Owned(format!(
                        "The type `{}` doesn't have this attribute, nor is it allowed on `null` values",
                        ty.meta.path
                    ))
                }
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
                    types::TypeKind::Or(variants) => get_suggestions(
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
            ConversionError::VariantErrors { variant_errors, .. } => {
                let mut errors = Vec::new();

                for (ty, error) in variant_errors {
                    let general = error.msg_general(ctx);

                    errors.push((
                        Spanned::new(
                            self.span,
                            Cow::Owned(format!(
                                "Failed parsing this as the variant `{}`: {general}",
                                types.key_type(*ty).meta.path,
                            )),
                        ),
                        Level::Error,
                    ));

                    errors.extend(error.msgs_specific(ctx));
                }

                return errors;
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
            ConversionError::NotNullable(_) => Cow::Borrowed("This value is `null`"),
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
            ConversionError::Custom(custom) => return custom.labels.clone(),
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

pub(super) type Result<T> = std::result::Result<T, Spanned<ConversionError>>;

impl From<Spanned<crate::path::PathError>> for Spanned<ConversionError> {
    fn from(value: Spanned<crate::path::PathError>) -> Self {
        value.map(ConversionError::PathError)
    }
}
