use std::collections::HashSet;

use proc_macro2::{Ident, Span, TokenStream};
use quote::quote;
use syn::{
    parse2, AttrStyle, Attribute, Data, DeriveInput, Error, Expr, Fields, ImplGenerics, Index,
    Token, Type, WhereClause, spanned::Spanned,
};

// Related fields used by `derive_struct` and `derive_fields` containing type info
struct TypeInfo<'a> {
    // The struct or variant, used for construction
    ty: proc_macro2::TokenStream,
    // The type's generics
    impl_generics: &'a ImplGenerics<'a>,
    where_clause: Option<&'a WhereClause>,
}

// Generate code to deserialize a struct or variant with fields
fn derive_fields(
    TypeInfo {
        ty,
        impl_generics,
        where_clause,
    }: TypeInfo,
    // The struct or variant's fields
    fields: &Fields,
    // Whether the struct or variant should be parsed from a tuple. For structs with named
    // fields, this is the case if it has the `tuple` attribute
    tuple: bool,
) -> proc_macro2::TokenStream {
    // General kind of field
    enum FieldTy<'a> {
        // The field may be deserialized from `bauble`, and must implement `FromBauble`
        Val {
            // An expression to generate this type. If `Some`, the field does not need to be
            // specified in `bauble`.
            default: Option<proc_macro2::TokenStream>,
            // Whether the field is a `bauble` attribute
            attribute: bool,
            // Index for a tuple that holds the values of deserializable fields
            index: Index,
            // Type from which the field is deserialized
            ty: &'a Type,
        },
        // The field is only generated from a default expression
        AsDefault {
            // An expression to generate this type
            default: proc_macro2::TokenStream,
            // Type from which the field is deserialized
            ty: &'a Type,
        },
    }

    // Information about a field collected from its attributes
    struct FieldAttrs<'a> {
        name: proc_macro2::TokenStream,
        ty: FieldTy<'a>,
    }

    let mut val_count = 0;

    // Parse the fields and attributes
    let fields = match fields
        .iter()
        .enumerate()
        .map(|(index, field)| -> Result<_, proc_macro2::TokenStream> {
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
                                as_default = Some(quote! { ::std::default::Default::default() });
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
                                Err(meta.error("expected no arguments for `attribute` attribute"))?
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
        .collect::<Result<Vec<_>, _>>()
    {
        Ok(fields) => fields,
        Err(err) => return err,
    };

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
        match &field.ty {
            FieldTy::Val {
                default: None,
                attribute: true,
                ..
            } => Some(quote! {
                attributes
                    .remove(stringify!(#name))
                    .ok_or_else(|| ::bauble::DeserializeError::MissingAttribute {
                        attribute: stringify!(#name).to_owned(),
                        ty: self_type_info.clone(),
                        span,
                    })?
            }),
            FieldTy::Val {
                default: Some(_),
                attribute: true,
                ..
            } => Some(quote! {
                attributes
                    .remove(stringify!(#name))
            }),
            FieldTy::Val {
                default: None,
                attribute: false,
                ..
            } => Some(match tuple {
                true => {
                    curr_value += 1;
                    quote! {
                        fields
                            .next()
                            .ok_or_else(|| ::bauble::DeserializeError::WrongTupleLength {
                                expected: #val_count,
                                found: #curr_value,
                                ty: self_type_info.clone(),
                                span,
                            })?
                    }
                }
                false => quote! {
                    fields
                        .remove(stringify!(#name))
                        .ok_or_else(|| ::bauble::DeserializeError::MissingField {
                            field: stringify!(#name).to_owned(),
                            ty: self_type_info.clone(),
                            span,
                        })?
                },
            }),
            FieldTy::Val {
                default: Some(_),
                attribute: false,
                ..
            } => {
                let default = Ident::new(&format!("default_{name}"), Span::call_site());
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
            FieldTy::AsDefault { .. } => None,
        }
    });

    // TODO: `var.function()` calls should be replaced with `TypeOrTrait::function(var)`
    // Generate code that checks for unexpected fields (also contains previously generated field
    // deserialization)
    let values = match tuple {
        true => quote! {
            let mut fields = fields.into_iter();
            let values = (#( #values, )*);

            let length = fields.len();
            if length != 0 {
                ::std::result::Result::Err(::bauble::DeserializeError::WrongTupleLength {
                    expected: #field_count,
                    found: #val_count + length,
                    ty: self_type_info.clone(),
                    span,
                })?
            }
        },
        false => quote! {
            let values = (#( #values, )*);

            if let ::std::option::Option::Some((field, _)) = fields.into_iter().next() {
                ::std::result::Result::Err(::bauble::DeserializeError::UnexpectedField {
                    field,
                    ty: self_type_info.clone(),
                })?
            }
        },
    };

    // Generate code that evaluates each field
    let fields = fields.iter().map(|field| {
        let ident = &field.name;
        let default = Ident::new(&format!("default_{ident}"), Span::call_site());
        match &field.ty {
            FieldTy::Val {
                default: Some(_),
                index,
                ..
            } => quote! {
                #ident: match values.#index {
                    Some(value) => ::bauble::BaubleAllocator::validate(
                        allocator,
                        ::bauble::FromBauble::from_bauble(value, allocator)?,
                    )?,
                    None => #default(),
                }
            },
            FieldTy::Val {
                default: None,
                index,
                ..
            } => quote! {
                #ident: ::bauble::BaubleAllocator::validate(
                    allocator,
                    ::bauble::FromBauble::from_bauble(values.#index, allocator)?
                )?
            },
            FieldTy::AsDefault { .. } => quote! { #ident: #default() },
        }
    });

    // Assemble the deserialization code, including a check for unexpected attributes
    quote! {
        #( #defaults )*

        #values

        if let ::std::option::Option::Some((attribute, _)) = attributes.into_iter().next() {
            ::std::result::Result::Err(::bauble::DeserializeError::UnexpectedAttribute {
                attribute,
                ty: self_type_info.clone(),
            })?
        }

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
fn derive_struct(
    ty_info: TypeInfo,
    // struct / variant level attributes
    attributes: Vec<Ident>,
    fields: &Fields,
) -> proc_macro2::TokenStream {
    let mut tuple = false;

    for attribute in attributes {
        match attribute.to_string().as_str() {
            "tuple" => tuple = true,
            // The other type attributes are handled earlier and are not included here
            _ => return Error::new_spanned(attribute, "unknown attribute").to_compile_error(),
        }
    }

    let fields_ty = match fields {
        // Named fields in a type with the `tuple` attribute are treated as a tuple
        Fields::Named(_) => Some(tuple),
        Fields::Unnamed(_) => Some(true),
        Fields::Unit => None,
    };

    let pattern = match fields_ty {
        Some(false) => quote! { ::bauble::FieldsKind::Struct(mut fields) },
        Some(true) => quote! { ::bauble::FieldsKind::Tuple(mut fields) },
        None => quote! { ::bauble::FieldsKind::Unit },
    };

    let fields = match fields_ty {
        Some(tuple) => derive_fields(ty_info, fields, tuple),
        None => {
            // The struct or variant is a unit, so generate very basic deserialization
            let TypeInfo { ty, .. } = ty_info;
            quote! {
                unsafe { ::bauble::BaubleAllocator::wrap(allocator, #ty) }
            }
        }
    };

    quote! {
        #pattern => {
            #fields
        },
    }
}

// Convert attributes to a list of identifiers, checking for duplicates and unexpected arguments
fn parse_attributes(attributes: &Vec<Attribute>) -> Result<Vec<Ident>, proc_macro2::TokenStream> {
    let mut found = HashSet::<_>::default();
    Ok(match attributes
        .into_iter()
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

                if found.insert(ident.to_string()) {
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
        Err(err) => return Err(err.to_compile_error()),
    }
    .into_iter()
    .flatten()
    .collect())
}

pub fn derive_bauble_derive_input(ast: &DeriveInput) -> TokenStream {
    // Type-level attributes
    // For an enum, whether the variant's field is directly deserialized in this type's place
    let mut flatten = false;
    // An allocator type override
    let mut allocator = None;
    // Attributes that are not type-level
    let mut attributes = vec![];

    // Parse attributes
    for attr in &ast.attrs {
        if !attr.path().is_ident("bauble") {
            continue;
        }

        if let AttrStyle::Inner(_) = attr.style {
            return Error::new_spanned(attr, "inner attributes are not supported")
                .to_compile_error()
                .into();
        }

        match attr.parse_nested_meta(|meta| {
            let Some(ident) = meta.path.get_ident() else {
                Err(meta.error("path must be an identifier"))?
            };

            match ident.to_string().as_str() {
                "flatten" => {
                    if flatten {
                        Err(meta.error("duplicate `flatten` attribute"))?
                    }

                    flatten = true;

                    if !meta.input.is_empty() && !meta.input.peek(Token![,]) {
                        Err(meta.error("unexpected token after flatten"))?
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
                _ => {
                    attributes.push(ident.clone());
                    Ok(())
                }
            }
        }) {
            Ok(()) => (),
            Err(err) => return err.to_compile_error().into(),
        }
    }

    let allocator = allocator.unwrap_or_else(|| quote! { ::bauble::DefaultAllocator });

    let (_, ty_generics, where_clause) = ast.generics.split_for_impl();

    let mut generics = ast.generics.clone();

    let lifetime = syn::Lifetime::new("'alloc_lifetime", generics.span());
    generics.params.push(syn::GenericParam::Lifetime(syn::LifetimeParam::new(lifetime.clone())));

    let (impl_generics, _, _) = generics.split_for_impl();

    let ident = &ast.ident;

    // Generate code to deserialize this type
    let match_value = if flatten {
        if let Some(attribute) = attributes.into_iter().next() {
            return Error::new_spanned(
                &attribute,
                format!("attribute `{attribute}` is incompatible with `flatten`"),
            )
            .to_compile_error()
            .into();
        }

        let Data::Enum(data) = &ast.data else {
            return Error::new(
                Span::call_site(),
                "`flatten` can only be used on enums",
            )
            .to_compile_error()
            .into();
        };

        let variants = match data
            .variants
            .iter()
            .map(|variant| -> Result<_, proc_macro2::TokenStream> {
                let ident = &variant.ident;

                let fields = derive_struct(
                    TypeInfo {
                        ty: quote! { Self::#ident },
                        impl_generics: &impl_generics,
                        where_clause,
                    },
                    parse_attributes(&variant.attrs)?,
                    &variant.fields,
                );

                Ok(quote! {
                    ::bauble::Value::Struct(type_info, fields) => {
                        match fields {
                            #fields
                            _ => Err(::bauble::DeserializeError::Custom {
                                message: format!(
                                    "No variant of `{}` matches the given data",
                                    stringify!(#ident),
                                ),
                                span,
                            })?,
                        }
                    },
                    _ => {
                        ::std::result::Result::Err(::bauble::DeserializeError::WrongKind {
                            ty: self_type_info.clone(),
                            expected: ::bauble::ValueKind::Enum,
                            found: value_kind,
                            span,
                        })?
                    }
                })
            })
            .collect::<Result<Vec<_>, _>>()
        {
            Ok(variants) => variants,
            Err(err) => return err.into(),
        };

        quote! {
            ::std::result::Result::Err(::bauble::DeserializeError::Custom {
                message: format!(
                    "No variant of `{}` matches the given data",
                    stringify!(#ident)
                ),
                span,
            })
            #(
                .or_else(|_| -> std::result::Result<
                    _,
                    std::boxed::Box<::bauble::DeserializeError>
                > {
                    let attributes = attributes.clone();
                    ::std::result::Result::Ok(
                        match value.clone() {
                            #variants
                        }
                    )
                })
            )*
        }
    } else {
        // The type is usual
        match &ast.data {
            Data::Struct(data) => {
                let case = derive_struct(
                    TypeInfo {
                        ty: quote! { Self },
                        impl_generics: &impl_generics,
                        where_clause,
                    },
                    attributes,
                    &data.fields,
                );

                quote! {
                    ::std::result::Result::Ok(match value {
                        ::bauble::Value::Struct(type_info, fields) => {
                            match fields {
                                #case
                                _ => ::std::result::Result::Err(::bauble::DeserializeError::WrongKind {
                                    expected: ::bauble::ValueKind::Struct,
                                    found: value_kind,
                                    ty: self_type_info.clone(),
                                    span,
                                })?,
                            }
                        }
                        _ => ::std::result::Result::Err(::bauble::DeserializeError::WrongKind {
                            expected: ::bauble::ValueKind::Struct,
                            found: value_kind,
                            ty: self_type_info.clone(),
                            span,
                        })?,
                    })
                }
            }
            Data::Enum(data) => {
                // enums don't accept any extra attributes on the type. Those attributes are on the
                // variants instead.
                if let Some(attribute) = attributes.into_iter().next() {
                    return Error::new_spanned(attribute, "unexpected attribute")
                        .to_compile_error()
                        .into();
                }

                let variant_convert = data.variants.iter().map(|variant| {
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

                                if found.insert(ident.to_string()) {
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
                        Err(err) => return err.to_compile_error(),
                    }
                    .into_iter()
                    .flatten()
                    .collect();

                    let derive = derive_struct(
                        TypeInfo {
                            ty: quote! { Self::#ident },
                            impl_generics: &impl_generics,
                            where_clause,
                        },
                        attributes,
                        &variant.fields,
                    );

                    quote! {
                        stringify!(#ident) => match fields {
                            #derive
                            _ => ::std::result::Result::Err(
                                ::bauble::DeserializeError::UnknownVariant {
                                    variant: name,
                                    kind: fields.variant_kind(),
                                    ty: self_type_info.clone(),
                                }
                            )?,
                        },
                    }
                });

                // Assemble the type's deserialization
                quote! {
                    ::std::result::Result::Ok(match value {
                        ::bauble::Value::Enum(type_info, name, fields) => {
                            match name.as_str() {
                                #(#variant_convert)*
                                _ => ::std::result::Result::Err(
                                    ::bauble::DeserializeError::UnknownVariant {
                                        variant: name,
                                        kind: fields.variant_kind(),
                                        ty: self_type_info.clone(),
                                    }
                                )?,
                            }
                        },
                        v => {
                            ::std::result::Result::Err(::bauble::DeserializeError::WrongKind {
                                expected: ::bauble::ValueKind::Enum,
                                found: v.kind(),
                                span,
                                ty: self_type_info.clone(),
                            })?
                        }
                    })
                }
            }
            Data::Union(data) => {
                Error::new_spanned(data.union_token, "unions are not supported").to_compile_error()
            }
        }
    };

    

    // Assemble the implementation
    quote! {
        impl #impl_generics ::bauble::FromBauble<#lifetime, #allocator> for #ident #ty_generics
            #where_clause
        {
            fn from_bauble(
                ::bauble::Val {
                    attributes: ::bauble::Spanned {
                        value: ::bauble::Attributes(mut attributes),
                        ..
                    },
                    value: ::bauble::Spanned { span, value },
                }: ::bauble::Val,
                allocator: &#lifetime #allocator,
            ) -> ::std::result::Result<
                <#allocator as ::bauble::BaubleAllocator>::Out<Self>,
                ::std::boxed::Box<::bauble::DeserializeError>
            > {
                let type_info = ::bauble::Spanned { span, value: value.type_info().cloned().unwrap_or_default() };
                let self_type_info = ::bauble::TypeInfo::new(module_path!(), stringify!(#ident));
                let value_kind = value.kind();
                if type_info.module != module_path!() || type_info.ident != stringify!(#ident) {
                    return ::std::result::Result::Err(
                        ::std::boxed::Box::new(::bauble::DeserializeError::WrongTypePath {
                            expected: self_type_info,
                            found: type_info,
                        })
                    )
                }
                #match_value
            }
        }
    }.into()
}

pub fn derive_bauble(input: TokenStream) -> TokenStream {
    let ast = match parse2::<DeriveInput>(input) {
        Ok(d) => d,
        Err(e) => {
            return e.to_compile_error();
        }
    };

    derive_bauble_derive_input(&ast)
}
