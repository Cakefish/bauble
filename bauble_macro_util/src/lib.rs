use std::collections::HashSet;

use proc_macro2::{Ident, Span, TokenStream};
use quote::{format_ident, quote, ToTokens};
use syn::{
    parenthesized, parse::Parse, parse2, punctuated::Punctuated, spanned::Spanned, token::PathSep,
    AttrStyle, Data, DeriveInput, Error, Expr, Fields, ImplGenerics, Index, PathSegment, Token,
    Type, WhereClause, WherePredicate,
};

/// General kind of field
enum FieldTy<'a> {
    /// The field may be deserialized from `bauble`, and must implement `FromBauble`
    Val {
        /// An expression to generate this type. If `Some`, the field does not need to be
        /// specified in `bauble`.
        default: Option<TokenStream>,
        /// Whether the field is a `bauble` attribute
        attribute: bool,
        /// Index for a tuple that holds the values of deserializable fields
        index: Index,
        /// Type from which the field is deserialized
        ty: &'a Type,
    },
    /// The field is only generated from a default expression
    AsDefault {
        /// An expression to generate this type
        default: TokenStream,
        /// Type from which the field is deserialized
        ty: &'a Type,
    },
}

/// Information about a field collected from its attributes
struct FieldAttrs<'a> {
    name: TokenStream,
    ty: FieldTy<'a>,
}

/// Information about a struct or variant's fields
struct FieldsInfo<'a> {
    fields: Vec<FieldAttrs<'a>>,
    val_count: usize,
    /// Whether the struct or variant has fields, and if so, whether it is a tuple
    ty: Option<bool>,
}

// Parse the attributes of a struct or variant's fields
fn parse_fields(
    // The struct or variant's fields
    fields: &Fields,
    // struct / variant level attributes
    attributes: Vec<Ident>,
) -> Result<FieldsInfo, TokenStream> {
    let mut tuple = false;

    for attribute in attributes {
        match attribute.to_string().as_str() {
            "tuple" => {
                if !tuple {
                    tuple = true;
                } else {
                    return Err(
                        Error::new_spanned(attribute, "Multiple tuple tags").to_compile_error()
                    );
                }
            }
            // The other type attributes are handled earlier and are not included here
            _ => return Err(Error::new_spanned(attribute, "unknown attribute").to_compile_error()),
        }
    }

    let mut val_count = 0;

    Ok(FieldsInfo {
        fields: fields
            .iter()
            .enumerate()
            .map(|(index, field)| -> Result<_, TokenStream> {
                let mut default = None;
                let mut as_default = None;
                let mut attribute = false;

                for attr in &field.attrs {
                    if !attr.path().is_ident("bauble") {
                        continue;
                    }

                    if let AttrStyle::Inner(_) = attr.style {
                        Err(
                            Error::new_spanned(attr, "inner attributes are not supported")
                                .to_compile_error(),
                        )?
                    }

                    attr.parse_nested_meta(|meta| {
                        let Some(ident) = meta.path.get_ident() else {
                            Err(meta.error("path must be an identifier"))?
                        };

                        match ident.to_string().as_str() {
                            "default" => {
                                if default.is_some() {
                                    Err(meta.error("duplicate `default` attribute"))?
                                }

                                if meta.input.parse::<Token![=]>().is_ok() {
                                    let expr = meta.input.parse::<Expr>()?;
                                    default = Some(quote! { #expr });
                                } else {
                                    default = Some(quote! { ::std::default::Default::default() });
                                }

                                if !meta.input.is_empty() && !meta.input.peek(Token![,]) {
                                    Err(meta.error("unexpected token after default value"))?
                                }

                                Ok(())
                            }
                            "as_default" => {
                                if as_default.is_some() {
                                    Err(meta.error("duplicate `as_default` attribute"))?
                                }

                                if meta.input.parse::<Token![=]>().is_ok() {
                                    let expr = meta.input.parse::<Expr>()?;
                                    as_default = Some(quote! { #expr });
                                } else {
                                    as_default =
                                        Some(quote! { ::std::default::Default::default() });
                                }

                                if !meta.input.is_empty() && !meta.input.peek(Token![,]) {
                                    Err(meta.error("unexpected token after default value"))?
                                }

                                Ok(())
                            }
                            "attribute" => {
                                if attribute {
                                    Err(meta.error("duplicate `attribute` attribute"))?
                                }

                                if !meta.input.is_empty() && !meta.input.peek(Token![,]) {
                                    Err(meta
                                        .error("expected no arguments for `attribute` attribute"))?
                                }

                                attribute = true;

                                Ok(())
                            }
                            ident => Err(meta.error(format!("unknown attribute `{ident}`"))),
                        }
                    })
                    .map_err(|err| err.to_compile_error())?;
                }

                Ok(FieldAttrs {
                    name: match &field.ident {
                        Some(ident) => quote! { #ident },
                        // Tuple structs are constructed with `MyType { 0: val0, 1: val1, ... }` syntax
                        None => {
                            let index = Index::from(index);
                            quote! { #index }
                        }
                    },
                    ty: match (default, as_default, attribute) {
                        (Some(_), Some(_), _) => Err(Error::new_spanned(
                            field,
                            "field cannot be both `default` and `as_default`",
                        )
                        .to_compile_error())?,
                        (_, Some(_), true) => Err(Error::new_spanned(
                            field,
                            "field cannot be both `as_default` and `attribute`",
                        )
                        .to_compile_error())?,
                        (None, Some(as_default), false) => FieldTy::AsDefault {
                            default: as_default,
                            ty: &field.ty,
                        },
                        (default, None, attribute) => {
                            let index = Index::from(val_count);
                            val_count += 1;

                            FieldTy::Val {
                                default,
                                attribute,
                                index,
                                ty: &field.ty,
                            }
                        }
                    },
                })
            })
            .collect::<Result<_, _>>()?,
        val_count,
        ty: match fields {
            // Named fields in a type with the `tuple` attribute are treated as a tuple
            Fields::Named(_) => Some(tuple),
            Fields::Unnamed(_) => Some(true),
            Fields::Unit => None,
        },
    })
}

/// Related fields used by `derive_struct` and `derive_fields` containing type info
struct TypeInfo<'a> {
    /// The struct or variant, used for construction
    ty: TokenStream,
    /// The type's generics
    impl_generics: &'a ImplGenerics<'a>,
    has_generics: bool,
    where_clause: &'a WhereClause,
}

// Generate code to deserialize a struct or variant with fields
fn derive_fields(
    TypeInfo {
        ty,
        impl_generics,
        has_generics,
        where_clause,
    }: TypeInfo,
    // The struct or variant's fields
    FieldsInfo {
        fields, val_count, ..
    }: &FieldsInfo,
    // Whether the struct or variant should be parsed from a tuple. For structs with named
    // fields, this is the case if it has the `tuple` attribute
    tuple: bool,
    // Whether the type should be flattened, passing its value and attributes directly to its field
    flatten: bool,
) -> TokenStream {
    let &val_count = val_count;

    // Generate functions for default values
    let defaults = fields.iter().filter_map(|field| match &field.ty {
        FieldTy::Val {
            default: Some(default),
            ty,
            ..
        }
        | FieldTy::AsDefault { default, ty } => {
            let name = Ident::new(&format!("default_{}", field.name), Span::call_site());
            Some(quote! {
                fn #name #impl_generics() -> #ty #where_clause {
                    #default
                }
            })
        }
        FieldTy::Val { default: None, .. } => None,
    });

    let field_count = fields.len();

    // Generate code that gets values for all fields that may be deserialized
    let mut curr_value = 0usize;
    let values = fields.iter().filter_map(|field| {
        let name = &field.name;
        match (&field.ty, flatten) {
            (
                FieldTy::Val {
                    default: None,
                    attribute: true,
                    ..
                },
                _,
            ) => Some(quote! {
                attributes
                    .remove(stringify!(#name))
                    .ok_or_else(|| ::bauble::DeserializeError::MissingAttribute {
                        attribute: stringify!(#name).to_owned(),
                        ty: Self::INFO.to_owned(),
                        span,
                    })?
            }),
            (
                FieldTy::Val {
                    default: Some(_),
                    attribute: true,
                    ..
                },
                _,
            ) => Some(quote! {
                attributes
                    .remove(stringify!(#name))
            }),
            (
                FieldTy::Val {
                    attribute: false, ..
                },
                true,
            ) => Some(quote! { () }),
            (
                FieldTy::Val {
                    default: None,
                    attribute: false,
                    ..
                },
                false,
            ) => Some(match tuple {
                true => {
                    curr_value += 1;
                    quote! {
                        fields
                            .next()
                            .ok_or_else(|| ::bauble::DeserializeError::WrongTupleLength {
                                expected: #val_count,
                                found: #curr_value,
                                ty: Self::INFO.to_owned(),
                                span,
                            })?
                    }
                }
                false => quote! {
                    fields
                        .remove(stringify!(#name))
                        .ok_or_else(|| ::bauble::DeserializeError::MissingField {
                            field: stringify!(#name).to_owned(),
                            ty: Self::INFO.to_owned(),
                            span,
                        })?
                },
            }),
            (
                FieldTy::Val {
                    default: Some(_),
                    attribute: false,
                    ..
                },
                false,
            ) => {
                let default = format_ident!("default_{name}");
                Some(match tuple {
                    true => {
                        curr_value += 1;
                        quote! {
                            fields
                                .next()
                                .unwrap_or_else(|| #default())
                        }
                    }
                    false => quote! {
                        fields
                            .remove(stringify!(#name))
                    },
                })
            }
            (FieldTy::AsDefault { .. }, _) => None,
        }
    });

    // TODO: `var.function()` calls should be replaced with `TypeOrTrait::function(var)`
    // Generate code that checks for unexpected fields (also contains previously generated field
    // deserialization)
    let values = match (tuple, flatten) {
        (_, true) => quote! { let values = (#( #values, )*); },
        (true, false) => quote! {
            let mut fields = fields.into_iter();
            let values = (#( #values, )*);

            let length = fields.len();
            if length != 0 {
                ::std::result::Result::Err(::bauble::DeserializeError::WrongTupleLength {
                    expected: #field_count,
                    found: #val_count + length,
                    ty: Self::INFO.to_owned(),
                    span,
                })?
            }
        },
        (false, false) => quote! {
            let values = (#( #values, )*);

            if let ::std::option::Option::Some((field, _)) = fields.into_iter().next() {
                ::std::result::Result::Err(::bauble::DeserializeError::UnexpectedField {
                    field,
                    ty: Self::INFO.to_owned(),
                })?
            }
        },
    };

    let check_attributes = (!flatten).then(|| {
        quote! {
            if let ::std::option::Option::Some((attribute, _)) = attributes.into_iter().next() {
                ::std::result::Result::Err(::bauble::DeserializeError::UnexpectedAttribute {
                    attribute,
                    ty: Self::INFO.to_owned(),
                })?
            }
        }
    });

    // Generate code that evaluates each field
    // TODO The way `impl_generics` is used here prevents the user from adding bounds directly on
    // the type parameters

    let fields = fields.iter().map(|field| {
        let ident = &field.name;
        let default = format_ident!("default_{ident}");
        let default_call = if has_generics {
            quote! { #default::#impl_generics() }
        } else {
            quote! { #default() }
        };
        match (&field.ty, flatten) {
            (
                FieldTy::Val {
                    attribute: false, ..
                },
                true,
            ) => quote! {
                #ident: ::bauble::BaubleAllocator::validate(
                    allocator,
                    ::bauble::FromBauble::from_bauble(::bauble::Val {
                        attributes: ::bauble::Spanned {
                            value: ::bauble::Attributes(attributes),
                            span: attributes_span,
                        },
                        value: ::bauble::Spanned { value, span },
                    }, allocator)?,
                )?
            },
            (
                FieldTy::Val {
                    default: Some(_),
                    index,
                    ..
                },
                false,
            )
            | (
                FieldTy::Val {
                    default: Some(_),
                    index,
                    attribute: true,
                    ..
                },
                true,
            ) => quote! {
                #ident: match values.#index {
                    Some(value) => ::bauble::BaubleAllocator::validate(
                        allocator,
                        ::bauble::FromBauble::from_bauble(value, allocator)?,
                    )?,
                    None => #default_call,
                }
            },
            (
                FieldTy::Val {
                    default: None,
                    index,
                    ..
                },
                false,
            )
            | (
                FieldTy::Val {
                    default: None,
                    index,
                    attribute: true,
                    ..
                },
                true,
            ) => quote! {
                #ident: ::bauble::BaubleAllocator::validate(
                    allocator,
                    ::bauble::FromBauble::from_bauble(values.#index, allocator)?
                )?
            },
            (FieldTy::AsDefault { .. }, _) => quote! { #ident: #default_call },
        }
    });

    // Assemble the deserialization code, including a check for unexpected attributes
    quote! {
        #( #defaults )*

        #values

        #check_attributes

        unsafe {
            ::bauble::BaubleAllocator::wrap(
                allocator,
                #ty {
                    #( #fields, )*
                }
            )
        }
    }
}

// Generate code to deserialize a struct or variant. See `derive_fields` for more field docs.
fn derive_struct(ty_info: TypeInfo, fields: &FieldsInfo, flatten: bool) -> TokenStream {
    let pattern = match fields.ty {
        Some(false) => quote! { ::bauble::FieldsKind::Struct(mut fields) },
        Some(true) => quote! { ::bauble::FieldsKind::Tuple(mut fields) },
        None => quote! { ::bauble::FieldsKind::Unit },
    };

    let fields = match fields.ty {
        Some(tuple) => derive_fields(ty_info, fields, tuple, flatten),
        None => {
            // The struct or variant is a unit, so generate very basic deserialization
            let TypeInfo { ty, .. } = ty_info;
            quote! {
                unsafe { ::bauble::BaubleAllocator::wrap(allocator, #ty) }
            }
        }
    };

    match flatten {
        true => quote! {
            #fields
        },
        false => quote! {
            #pattern => {
                #fields
            },
        },
    }
}

fn flattened_ty<'a, T: ToTokens>(span: T, fields: &'a FieldsInfo) -> Result<&'a Type, TokenStream> {
    match fields
        .fields
        .iter()
        .try_fold(None, |acc, field| match (acc, &field.ty) {
            (
                Some(_),
                FieldTy::Val {
                    attribute: false,
                    ty,
                    ..
                },
            ) => Err(Error::new_spanned(ty, "only one field may be flattened")),
            (
                acc @ Some(_),
                FieldTy::Val {
                    attribute: true, ..
                }
                | FieldTy::AsDefault { .. },
            ) => Ok(acc),
            (
                None,
                FieldTy::Val {
                    attribute: false,
                    ty,
                    ..
                },
            ) => Ok(Some(ty)),
            (
                None,
                FieldTy::Val {
                    attribute: true, ..
                }
                | FieldTy::AsDefault { .. },
            ) => Ok(None),
        }) {
        Ok(Some(ty)) => Ok(ty),
        Ok(None) => {
            Err(Error::new_spanned(span, "at least one field must be flattened").to_compile_error())
        }
        Err(err) => Err(err.to_compile_error()),
    }
}

pub fn derive_bauble_derive_input(
    ast: &DeriveInput,
    mut allocator: Option<TokenStream>,
) -> TokenStream {
    // Type-level attributes
    // For an enum, whether the variant's field is directly deserialized in this type's place
    let mut flatten = false;
    // Additional bounds on the `impl`
    let mut bounds = None;
    // Override for the module's path
    let mut path = None;
    // Override for the type's name
    let mut rename = None;
    // Attributes that are not type-level
    let mut attributes = vec![];
    // Set this typeinfo to always be a reference.
    let mut always_ref = false;

    // Parse attributes
    for attr in &ast.attrs {
        if !attr.path().is_ident("bauble") {
            continue;
        }

        if let AttrStyle::Inner(_) = attr.style {
            return Error::new_spanned(attr, "inner attributes are not supported")
                .to_compile_error();
        }

        let nested_meta = attr.parse_nested_meta(|meta| {
            let Some(ident) = meta.path.get_ident() else {
                Err(meta.error("path must be an identifier"))?
            };

            match ident.to_string().as_str() {
                "flatten" => {
                    if always_ref {
                        Err(meta.error("`flatten` and `always_ref` are incompatible"))?
                    }
                    if flatten {
                        Err(meta.error("duplicate `flatten` attribute"))?
                    }

                    flatten = true;

                    if !meta.input.is_empty() && !meta.input.peek(Token![,]) {
                        Err(meta.error("unexpected token after flatten"))?
                    }

                    Ok(())
                }
                "bounds" => {
                    if bounds.is_some() {
                        Err(meta.error("duplicate `bounds` attribute"))?
                    }

                    meta.input.parse::<Token![=]>()?;
                    let bounds_parse;
                    parenthesized!(bounds_parse in meta.input);
                    bounds = Some(bounds_parse.parse_terminated(WherePredicate::parse, Token![,])?);

                    if !meta.input.is_empty() && !meta.input.peek(Token![,]) {
                        Err(meta.error("unexpected token after bounds"))?
                    }

                    Ok(())
                }
                "path" => {
                    if path.is_some() {
                        Err(meta.error("duplicate `path` attribute"))?
                    }

                    meta.input.parse::<Token![=]>()?;
                    path = Some(
                        Punctuated::<PathSegment, PathSep>::parse_separated_nonempty(meta.input)?,
                    );

                    if !meta.input.is_empty() && !meta.input.peek(Token![,]) {
                        Err(meta.error("unexpected token after path"))?
                    }

                    Ok(())
                }
                "rename" => {
                    if rename.is_some() {
                        Err(meta.error("duplicate `rename` attribute"))?
                    }

                    meta.input.parse::<Token![=]>()?;
                    rename = Some(meta.input.parse::<Ident>()?);

                    if !meta.input.is_empty() && !meta.input.peek(Token![,]) {
                        Err(meta.error("unexpected token after rename"))?
                    }

                    Ok(())
                }
                "allocator" => {
                    if allocator.is_some() {
                        Err(meta.error("duplicate `allocator` attribute"))?
                    }

                    meta.input.parse::<Token![=]>()?;
                    let expr = meta.input.parse::<Expr>()?;
                    allocator = Some(quote! { #expr });

                    if !meta.input.is_empty() && !meta.input.peek(Token![,]) {
                        Err(meta.error("unexpected token after allocator"))?
                    }

                    Ok(())
                }
                "always_ref" => {
                    if flatten {
                        Err(meta.error("`flatten` and `always_ref` are incompatible"))?
                    }
                    if always_ref {
                        Err(meta.error("duplicate `always_ref` attribute"))?
                    }

                    always_ref = true;

                    if !meta.input.is_empty() && !meta.input.peek(Token![,]) {
                        Err(meta.error("unexpected token after always_ref"))?
                    }

                    Ok(())
                }
                _ => {
                    attributes.push(ident.clone());
                    Ok(())
                }
            }
        });

        match nested_meta {
            Ok(()) => (),
            Err(err) => return err.to_compile_error(),
        }
    }

    let allocator = allocator.unwrap_or_else(|| quote! { ::bauble::DefaultAllocator });

    let (impl_generics, ty_generics, where_clause) = ast.generics.split_for_impl();
    let mut where_clause = where_clause.cloned().unwrap_or_else(|| WhereClause {
        where_token: Default::default(),
        predicates: Default::default(),
    });
    if let Some(bounds) = bounds {
        where_clause.predicates.extend(bounds);
    }

    let mut generics = ast.generics.clone();

    let lifetime = syn::Lifetime::new("'alloc_lifetime", generics.span());
    generics
        .params
        .push(syn::GenericParam::Lifetime(syn::LifetimeParam::new(
            lifetime.clone(),
        )));

    let (modified_impl_generics, _, _) = generics.split_for_impl();

    let ident = &ast.ident;
    let name = rename.as_ref().unwrap_or(ident);

    let path = match path {
        Some(path) => {
            // Unfortunately, `Punctuated<PathSegment, PathSep>` likes to insert spaces in `quote!`
            let path = path
                .iter()
                .map(|segment| segment.ident.to_string())
                .collect::<Vec<_>>()
                .join("::");

            quote! { #path }
        }
        None => quote! { module_path!() },
    };

    let mut field_attributes = Vec::new();

    // Generate code to deserialize this type
    let (type_info, match_value) = match &ast.data {
        Data::Struct(data) => {
            let fields = match parse_fields(&data.fields, attributes) {
                Ok(fields) => fields,
                Err(err) => return err,
            };

            for field in &fields.fields {
                if matches!(
                    field.ty,
                    FieldTy::Val {
                        attribute: true,
                        ..
                    }
                ) {
                    field_attributes.push(field.name.to_string());
                }
            }

            let case = derive_struct(
                TypeInfo {
                    ty: quote! { Self },
                    impl_generics: &impl_generics,
                    has_generics: generics.params.len() > 1,
                    where_clause: &where_clause,
                },
                &fields,
                flatten,
            );

            match flatten {
                true => {
                    let flattened_ty = match flattened_ty(ident, &fields) {
                        Ok(ty) => ty,
                        Err(err) => return err,
                    };

                    (
                        quote! {
                            ::bauble::TypeInfo::Flatten {
                                types: &[
                                    &<#flattened_ty as ::bauble::FromBauble<#lifetime, #allocator>>
                                        ::INFO,
                                ],
                                module: #path,
                                ident: stringify!(#name),
                                always_ref: false,
                            }
                        },
                        quote! { ::std::result::Result::Ok( { #case } ) },
                    )
                }
                false => (
                    quote! { ::bauble::TypeInfo::new(#path, stringify!(#name)) },
                    quote! {
                        ::std::result::Result::Ok(match value {
                            ::bauble::Value::Struct(type_info, fields) => {
                                match fields {
                                    #case
                                    _ => ::std::result::Result::Err(
                                        ::bauble::DeserializeError::WrongKind {
                                            expected: ::bauble::ValueKind::Struct,
                                            found: value_kind,
                                            ty: Self::INFO.to_owned(),
                                            span,
                                        }
                                    )?,
                                }
                            }
                            _ => ::std::result::Result::Err(::bauble::DeserializeError::WrongKind {
                                expected: ::bauble::ValueKind::Struct,
                                found: value_kind,
                                ty: Self::INFO.to_owned(),
                                span,
                            })?,
                        })
                    },
                ),
            }
        }
        Data::Enum(data) => {
            // enums don't accept any extra attributes on the type. Those attributes are on the
            // variants instead.
            if let Some(attribute) = attributes.into_iter().next() {
                return Error::new_spanned(attribute, "unexpected attribute").to_compile_error();
            }

            let (flattened_tys, variant_convert): (Vec<_>, Vec<_>) = data
                .variants
                .iter()
                .filter_map(|variant| {
                    let ident = &variant.ident;

                    // Parse variant attributes
                    let mut found = HashSet::<_>::default();
                    let attributes = match variant
                        .attrs
                        .iter()
                        .map(|attr| {
                            let mut attributes = Vec::default();

                            if !attr.path().is_ident("bauble") {
                                return Ok(attributes);
                            }

                            if let AttrStyle::Inner(_) = attr.style {
                                return Err(Error::new_spanned(
                                    attr,
                                    "inner attributes are not supported",
                                ));
                            }

                            attr.parse_nested_meta(|meta| {
                                let Some(ident) = meta.path.get_ident() else {
                                    Err(meta.error("path must be an identifier"))?
                                };

                                if !found.insert(ident.to_string()) {
                                    Err(meta.error("duplicate attribute"))?
                                }

                                if !meta.input.is_empty() && !meta.input.peek(Token![,]) {
                                    Err(meta.error("expected no arguments for attribute"))?
                                }

                                attributes.push(ident.clone());

                                Ok(())
                            })?;

                            Ok(attributes)
                        })
                        .collect::<Result<Vec<_>, _>>()
                    {
                        Ok(attributes) => attributes,
                        Err(err) => return Some((quote! {}, err.to_compile_error())),
                    }
                    .into_iter()
                    .flatten()
                    .collect::<Vec<Ident>>();

                    if attributes.iter().any(|attr| attr == "ignore") {
                        return None;
                    }

                    let fields = match parse_fields(&variant.fields, attributes) {
                        Ok(fields) => fields,
                        Err(err) => return Some((quote! {}, err)),
                    };
                    for field in &fields.fields {
                        if matches!(
                            field.ty,
                            FieldTy::Val {
                                attribute: true,
                                ..
                            }
                        ) {
                            field_attributes.push(field.name.to_string());
                        }
                    }
                    let derive = derive_struct(
                        TypeInfo {
                            ty: quote! { Self::#ident },
                            impl_generics: &impl_generics,
                            has_generics: generics.params.len() > 1,
                            where_clause: &where_clause,
                        },
                        &fields,
                        flatten,
                    );

                    match flatten {
                        true => {
                            let flattened_ty = match flattened_ty(variant, &fields) {
                                Ok(ty) => ty,
                                Err(err) => return Some((quote! {}, err)),
                            };

                            Some((
                                quote! { #flattened_ty },
                                quote! {
                                    if <#flattened_ty as ::bauble::FromBauble<
                                        #lifetime,
                                        #allocator
                                    >>::INFO.contains(&type_info) {
                                        #derive
                                    } else
                                },
                            ))
                        }
                        false => Some((
                            quote! {},
                            quote! {
                                stringify!(#ident) => match fields {
                                    #derive
                                    _ => ::std::result::Result::Err(
                                        ::bauble::DeserializeError::UnknownVariant {
                                            variant: name,
                                            kind: fields.variant_kind(),
                                            ty: Self::INFO.to_owned(),
                                        }
                                    )?,
                                },
                            },
                        )),
                    }
                })
                .unzip();

            // Assemble the type's deserialization
            match flatten {
                true => (
                    quote! {
                        ::bauble::TypeInfo::Flatten {
                            types: &[
                                #(&<#flattened_tys as ::bauble::FromBauble<#lifetime, #allocator>>::INFO,)*
                            ],
                            module: #path,
                            ident: stringify!(#name),
                            always_ref: false,
                        }
                    },
                    quote! {
                        ::std::result::Result::Ok(
                            // `if`-`else` chain because assoc consts can't be used in `match` arms :(
                            // https://github.com/rust-lang/rust/issues/72602
                            // TODO Perhaps this can be fixed by setting local `const`s
                            #(#variant_convert)* {
                                ::std::result::Result::Err(
                                    ::bauble::DeserializeError::UnknownFlattenedVariant {
                                        variant: type_info,
                                        ty: Self::INFO.to_owned(),
                                    }
                                )?
                            }
                        )
                    },
                ),
                false => (
                    quote! { ::bauble::TypeInfo::new(#path, stringify!(#name)) },
                    quote! {
                        ::std::result::Result::Ok(match value {
                            ::bauble::Value::Enum(type_info, name, fields) => {
                                match name.as_str() {
                                    #(#variant_convert)*
                                    _ => ::std::result::Result::Err(
                                        ::bauble::DeserializeError::UnknownVariant {
                                            variant: name,
                                            kind: fields.variant_kind(),
                                            ty: Self::INFO.to_owned(),
                                        }
                                    )?,
                                }
                            },
                            v => {
                                ::std::result::Result::Err(::bauble::DeserializeError::WrongKind {
                                    expected: ::bauble::ValueKind::Enum,
                                    found: v.kind(),
                                    span,
                                    ty: Self::INFO.to_owned(),
                                })?
                            }
                        })
                    },
                ),
            }
        }
        Data::Union(data) => (
            quote! {},
            Error::new_spanned(data.union_token, "unions are not supported").to_compile_error(),
        ),
    };

    let validate_type_info = (!flatten).then(|| {
        quote! {
            if !Self::INFO.contains(&type_info) {
                return ::std::result::Result::Err(
                    ::std::boxed::Box::new(::bauble::DeserializeError::WrongTypePath {
                        expected: Self::INFO.to_owned(),
                        found: type_info,
                    })
                )
            }
        }
    });

    let type_info = if always_ref {
        quote! {
            (#type_info).with_always_ref()
        }
    } else {
        type_info
    };

    let type_info = if field_attributes.is_empty() {
        type_info
    } else {
        quote! {
            (#type_info).with_attributes(&[#(#field_attributes),*])
        }
    };

    // Assemble the implementation
    quote! {
        #[automatically_derived]
        impl #modified_impl_generics ::bauble::FromBauble<#lifetime, #allocator>
            for #ident #ty_generics
            #where_clause
        {
            const INFO: ::bauble::TypeInfo<'static> = #type_info;

            fn from_bauble(
                ::bauble::Val {
                    attributes: ::bauble::Spanned {
                        value: ::bauble::Attributes(mut attributes),
                        span: attributes_span,
                    },
                    value: ::bauble::Spanned { span, value },
                }: ::bauble::Val,
                allocator: &#allocator,
            ) -> ::std::result::Result<
                <#allocator as ::bauble::BaubleAllocator<#lifetime>>::Out<Self>,
                ::std::boxed::Box<::bauble::DeserializeError>
            > {
                let value_kind = value.kind();
                let type_info = ::bauble::Spanned {
                    span,
                    value: value.type_info(),
                };

                #validate_type_info
                #match_value
            }
        }
    }
}

pub fn derive_bauble(input: TokenStream) -> TokenStream {
    let ast = match parse2::<DeriveInput>(input) {
        Ok(d) => d,
        Err(e) => {
            return e.to_compile_error();
        }
    };

    derive_bauble_derive_input(&ast, None)
}
