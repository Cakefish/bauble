use indexmap::IndexMap;
use proc_macro2::{Ident, Span, TokenStream};
use quote::{ToTokens, format_ident, quote};
use syn::{
    AttrStyle, Data, DeriveInput, Error, Expr, Fields, Index, Token, Type, WhereClause,
    WherePredicate, parse2, punctuated::Punctuated, spanned::Spanned, token::PathSep,
};

#[derive(Default, Clone)]
struct Extra(IndexMap<String, String>);

impl Extra {
    fn parse(&mut self, meta: syn::meta::ParseNestedMeta) -> syn::Result<()> {
        meta.parse_nested_meta(|meta| {
            let Some(ident) = meta.path.get_ident() else {
                Err(meta.error("path must be an identifier"))?
            };

            meta.input.parse::<Token![=]>()?;

            let s = meta.input.parse::<syn::LitStr>()?;

            if self.0.insert(ident.to_string(), s.value()).is_some() {
                Err(meta.error("duplicate extra field"))?
            }

            Ok(())
        })?;

        if !meta.input.is_empty() && !meta.input.peek(Token![,]) {
            Err(meta.error("Unexpected token after `extra` attribute"))?
        }

        Ok(())
    }

    fn convert(&self) -> TokenStream {
        let extra = self.0.iter().map(|(a, b)| {
            quote! { (::std::borrow::ToOwned::to_owned(#a), ::std::borrow::ToOwned::to_owned(#b)) }
        });

        quote! {
            ::bauble::private::IndexMap::from_iter([
                #(#extra),*
            ])
        }
    }
}

/// General kind of field
enum FieldTy<'a> {
    /// The field may be deserialized from `bauble`, and must implement `FromBauble`
    Val {
        /// An expression to generate this type. If `Some`, the field does not need to be
        /// specified in `bauble`.
        default: Option<TokenStream>,
        /// Whether the field is a `bauble` attribute, and if so which ident to use.
        attribute: Option<Ident>,
        /// A default bauble value for this field.
        value_default: Option<TokenStream>,
        extra: Extra,
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

impl FieldTy<'_> {
    fn get_type(&self) -> &Type {
        match self {
            FieldTy::Val { ty, .. } | FieldTy::AsDefault { ty, .. } => ty,
        }
    }
}

/// Information about a field collected from its attributes
struct FieldAttrs<'a> {
    name: TokenStream,
    ty: FieldTy<'a>,
}

impl FieldAttrs<'_> {
    fn variable_ident(&self) -> Ident {
        format_ident!("__field_{}", self.name.to_string())
    }
}

#[derive(Clone, Copy)]
enum FieldsKind {
    Unnamed,
    Named,
}

#[derive(Default)]
struct ContainerAttrs {
    // On container or type
    extra: Extra,
    rename: Option<Ident>,
    validate: Option<TokenStream>,
    flatten: bool,
    value_default: Option<TokenStream>,

    // On type
    traits: Vec<TokenStream>,
    from: Option<Type>,
    path: Option<String>,
    allocator: Option<TokenStream>,
    bounds: Option<Punctuated<WherePredicate, syn::token::Comma>>,
    nullable: Option<TokenStream>,

    // On Container
    tuple: bool,
}

enum ContainerType {
    Container,
    Type,
    Both,
}

impl ContainerType {
    fn is_container(&self) -> bool {
        matches!(self, Self::Container | Self::Both)
    }

    fn is_type(&self) -> bool {
        matches!(self, Self::Type | Self::Both)
    }
}

impl ContainerAttrs {
    fn validate(&self) -> syn::Result<()> {
        if let Some(from) = &self.from {
            if self.flatten {
                return Err(syn::Error::new_spanned(
                    from,
                    "The `flatten` and `from` attributes are incompatible",
                ));
            }
            if self.tuple {
                return Err(syn::Error::new_spanned(
                    from,
                    "The `tuple` and `from` attributes are incompatible",
                ));
            }
        }

        Ok(())
    }
    fn parse(
        attributes: &[syn::Attribute],
        kind: ContainerType,
        flatten: bool,
        from: Option<Type>,
        default: fn(TokenStream) -> TokenStream,
    ) -> syn::Result<Self> {
        let mut this = Self {
            flatten,
            from,
            ..Default::default()
        };

        for attr in attributes {
            if let syn::Meta::NameValue(syn::MetaNameValue {
                path,
                value:
                    Expr::Lit(syn::ExprLit {
                        lit: syn::Lit::Str(s),
                        ..
                    }),
                ..
            }) = &attr.meta
            {
                if path.is_ident("doc") {
                    this.extra.0.insert("doc".to_string(), s.value());
                }
                continue;
            }
            if !attr.path().is_ident("bauble") {
                continue;
            }

            attr.parse_nested_meta(|meta| {
                let Some(ident) = meta.path.get_ident() else {
                    Err(meta.error("Path must be an identifier"))?
                };

                match ident.to_string().as_str() {
                    "extra" => this.extra.parse(meta)?,
                    "rename" => {
                        if this.rename.is_some() {
                            Err(meta.error("Duplicate `rename` attribute"))?
                        }

                        this.rename = Some(meta.value()?.parse()?);
                    }
                    "flatten" => {
                        if this.flatten {
                            Err(meta.error("Duplicate `flatten` attribute"))?;
                        }

                        this.flatten = true;
                    }
                    "validate" => {
                        if this.validate.is_some() {
                            Err(meta.error("Duplicate `validate` attribute"))?
                        }

                        this.validate = Some(meta.value()?.parse()?);
                    }
                    "value_default" => {
                        if this.value_default.is_some() {
                            Err(meta.error("Duplicate `value_default` attribute"))?;
                        }

                        this.value_default = Some(meta.value()?.parse()?);
                    }
                    "traits" => {
                        if !kind.is_type() {
                            Err(meta.error("The `traits` attribute can only be used on types"))?
                        }
                        meta.parse_nested_meta(|meta| {
                            this.traits.push(meta.path.to_token_stream());

                            Ok(())
                        })?;
                    }
                    "path" => {
                        if !kind.is_type() {
                            Err(meta.error("The `path` attribute can only be used on types"))?
                        }

                        if this.path.is_some() {
                            Err(meta.error("Duplicate `path` attribute"))?
                        }

                        let path =
                            Punctuated::<Ident, PathSep>::parse_separated_nonempty(meta.value()?)?;

                        if path.is_empty() {
                            Err(meta.error("`path` attribute can't be empty"))?
                        }

                        if path.trailing_punct() {
                            Err(meta.error("`path` can't have a trailing path seperator"))?
                        }

                        let path = path
                            .iter()
                            .map(|segment| segment.to_string())
                            .collect::<Vec<_>>()
                            .join("::");

                        this.path = Some(path);
                    }
                    "from" => {
                        if !kind.is_type() {
                            Err(meta.error("The `from` attribute can only be used on types"))?
                        }

                        if this.from.is_some() {
                            Err(meta.error("Duplicate `from` attribute"))?
                        }

                        this.from = Some(meta.value()?.parse()?);
                    }

                    "allocator" => {
                        if !kind.is_type() {
                            Err(meta.error("The `allocator` attribute can only be used on types"))?
                        }

                        if this.allocator.is_some() {
                            Err(meta.error("Duplicate `allocator` attribute"))?
                        }

                        this.allocator = Some(meta.value()?.parse()?);
                    }

                    "bounds" => {
                        if !kind.is_type() {
                            Err(meta.error("The `bounds` attribute can only be used on types"))?
                        }

                        let bounds = this.bounds.get_or_insert_default();

                        meta.parse_nested_meta(|meta| {
                            bounds.push(meta.input.parse()?);
                            Ok(())
                        })?;
                    }
                    "nullable" => {
                        if !kind.is_type() {
                            Err(meta.error("The `nullable` attribute can only be used on types"))?
                        }
                        if this.nullable.is_some() {
                            Err(meta.error("Duplicate `nullable` attribute"))?
                        }

                        this.nullable = Some(match meta.value() {
                            Ok(meta) => {
                                let e: syn::Expr = meta.parse()?;
                                e.into_token_stream()
                            }
                            Err(_) => {
                                let default = default(quote! { Self });
                                quote! {
                                    // SAFETY: If this compiles we're using the default allocator, which is safe.
                                    |a| unsafe { ::bauble::BaubleAllocator::wrap(a, #default) }
                                }
                            }
                        });
                    }

                    "tuple" => {
                        if !kind.is_container() {
                            Err(meta.error("The `tuple` attribute can only be used on containers"))?
                        }

                        if this.tuple {
                            Err(meta.error("Duplicate `tuple` attribute"))?
                        }

                        this.tuple = true;
                    }

                    attr => {
                        Err(meta.error(format!("`{attr}` isn't a valid attribute for bauble")))?
                    }
                }

                Ok(())
            })?;
        }

        this.validate()?;

        Ok(this)
    }
}

/// Information about a struct or variant's fields
struct FieldsInfo<'a> {
    fields: Vec<FieldAttrs<'a>>,
    val_count: usize,
    /// Whether the struct or variant has fields, and if so, whether it is a tuple
    kind: Option<FieldsKind>,
    real_kind: Option<FieldsKind>,
}

// Parse the attributes of a struct or variant's fields
fn parse_fields(
    // The struct or variant's fields
    fields: &Fields,
    tuple: bool,
    has_from: bool,
    construct_default: fn(TokenStream) -> TokenStream,
) -> syn::Result<FieldsInfo> {
    let mut val_count = 0;
    let kind = match fields {
        // Named fields in a type with the `tuple` attribute are treated as a tuple
        Fields::Named(_) => Some(if tuple {
            FieldsKind::Unnamed
        } else {
            FieldsKind::Named
        }),
        Fields::Unnamed(_) => Some(FieldsKind::Unnamed),
        Fields::Unit => None,
    };
    let mut last = None;
    Ok(FieldsInfo {
        fields: fields
            .iter()
            .enumerate()
            .map(|(index, field)| -> syn::Result<_> {
                let mut default = None;
                let mut value_default = None;
                let mut as_default = None;
                let mut attribute = None;
                let mut extra = Extra::default();

                for attr in &field.attrs {
                    if let syn::Meta::NameValue(syn::MetaNameValue { path, value: Expr::Lit(syn::ExprLit { lit: syn::Lit::Str(s), .. }), .. }) = &attr.meta {
                        if path.is_ident("doc") {
                            extra.0.insert("doc".to_string(), s.value());
                        }
                        continue;
                    }
                    if !attr.path().is_ident("bauble") {
                        continue;
                    }

                    if let AttrStyle::Inner(_) = attr.style {
                        Err(
                            Error::new_spanned(attr, "inner attributes are not supported"),
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

                                default = Some(match meta.value() {
                                    Ok(input) => {
                                        let expr = input.parse::<Expr>()?;
                                        quote! { #expr }
                                    },
                                    Err(_) => construct_default(field.ty.to_token_stream()),
                                });

                                Ok(())
                            }
                            "as_default" => {
                                if as_default.is_some() {
                                    Err(meta.error("duplicate `as_default` attribute"))?
                                }

                                as_default = Some(match meta.value() {
                                    Ok(input) => {
                                        let expr = input.parse::<Expr>()?;
                                        quote! { #expr }
                                    },
                                    Err(_) => construct_default(field.ty.to_token_stream()),
                                });

                                Ok(())
                            }
                            "value_default" => {
                                if value_default.is_some() {
                                    Err(meta.error("duplicate `value_default` attribute"))?
                                }

                                let expr: Expr = meta.value()?.parse()?;
                                value_default = Some(quote! { #expr });

                                Ok(())
                            }
                            "attribute" => {
                                if attribute.is_some() {
                                    Err(meta.error("duplicate `attribute` attribute"))?
                                }

                                if meta.input.parse::<Token![=]>().is_ok() {
                                    let ident = meta.input.parse::<Ident>()?;
                                    attribute = Some(ident);
                                } else {
                                    attribute = Some(field.ident.clone().ok_or(meta.error("For unnamed fields the attribute specifier needs to be annotated with `attribute = ident`"))?);
                                }

                                Ok(())
                            }
                            "extra" => {
                                extra.parse(meta)
                            }
                            ident => Err(meta.error(format!("unknown attribute `{ident}`"))),
                        }
                    })?;
                }

                let field = FieldAttrs {
                    name: match &field.ident {
                        Some(ident) => quote! { #ident },
                        // Tuple structs are constructed with `MyType { 0: val0, 1: val1, ... }` syntax
                        None => {
                            let index = Index::from(index);
                            quote! { #index }
                        }
                    },
                    ty: match (default, as_default, attribute, value_default) {
                        (Some(_), Some(_), _, _) => Err(Error::new_spanned(
                            field,
                            "field cannot be both `default` and `as_default`",
                        )
                        )?,
                        (Some(_), _, _, Some(_)) => Err(Error::new_spanned(
                            field,
                            "field cannot be both `default` and have `value_default`",
                        )
                        )?,
                        (_, Some(_), Some(_), _) => Err(Error::new_spanned(
                            field,
                            "field cannot be both `as_default` and `attribute`",
                        )
                        )?,
                        (_, Some(_), _, Some(_)) => Err(Error::new_spanned(
                            field,
                            "field cannot be both `as_default` and have `value_default`",
                        )
                        )?,
                        (None, Some(as_default), None, None) => FieldTy::AsDefault {
                            default: as_default,
                            ty: &field.ty,
                        },
                        (default, None, attribute, value_default) => {
                            if matches!(kind, Some(FieldsKind::Unnamed)) && attribute.is_none() {
                                if default.is_some() {
                                    last = Some(field.span());
                                } else if let Some(span) = last {
                                    Err(Error::new(span, "Optional unnamed fields have to be at the end"))?
                                }
                            }
                            if attribute.is_none() {
                                val_count += 1;

                                if has_from && (default.is_some() || !extra.0.is_empty()) {
                                    Err(Error::new(field.span(), "This field won't be parsed from bauble as there is a `from` attribute on the type"))?
                                }
                            }

                            FieldTy::Val {
                                default,
                                attribute,
                                ty: &field.ty,
                                value_default,
                                extra,
                            }
                        }
                    },
                };

                Ok(field)
            })
            .collect::<syn::Result<_>>()?,
        val_count,
        real_kind: match fields {
            Fields::Named(_) => Some(FieldsKind::Named),
            Fields::Unnamed(_) => Some(FieldsKind::Unnamed),
            Fields::Unit => None,
        },
        kind,
    })
}

/// Related fields used by `derive_struct` and `derive_fields` containing type info
struct TypeInfo {
    span: Span,
    /// The struct or variant, used for construction
    ty: TokenStream,
    allocator: TokenStream,
    // /// The type's generics
    // impl_generics: &'a ImplGenerics<'a>,
    // has_generics: bool,
    // where_clause: &'a WhereClause,
}

fn from_bauble(v: impl ToTokens) -> TokenStream {
    quote! {
        ::bauble::Bauble::from_bauble(#v, __allocator).and_then(|__res|
            // SAFETY: We only use this allocator.
            unsafe { ::bauble::BaubleAllocator::validate(__allocator, __res) }
        )
    }
}

fn derive_fields(
    ty_info: &TypeInfo,
    fields: &FieldsInfo,
    construct: &TokenStream,
    flatten: bool,
) -> (Option<(TokenStream, TokenStream)>, TokenStream) {
    let allocator = &ty_info.allocator;
    match (fields.kind, flatten) {
        (_, true) if fields.val_count == 1 => {
            let field = fields
                .fields
                .iter()
                .find(|field| {
                    matches!(
                        field.ty,
                        FieldTy::Val {
                            attribute: None,
                            ..
                        }
                    )
                })
                .expect("val_count is 1");
            let ty = field.ty.get_type();
            let ident = field.variable_ident();
            let v = from_bauble(quote!(*#ident));
            (
                Some((
                    quote! {
                        ::bauble::Value::Transparent(#ident)
                    },
                    quote! {
                        {
                            let #ident = #v?;

                            #construct
                        }
                    },
                )),
                quote! {
                    ::bauble::types::TypeKind::Transparent(registry.get_or_register_type::<#ty, #allocator>())
                },
            )
        }
        (None, true) => (
            None,
            quote! {
                ::bauble::types::TypeKind::Primitive(::bauble::types::Primitive::Unit)
            },
        ),
        (None, false) => (
            None,
            quote! { ::bauble::types::TypeKind::Struct(::bauble::types::Fields::Unit) },
        ),
        (Some(FieldsKind::Unnamed), flatten) => {
            let mut required_fields = Vec::new();
            let mut optional_fields = Vec::new();
            let mut field_constructors = Vec::new();
            for field in &fields.fields {
                if let FieldTy::Val {
                    default,
                    attribute: None,
                    extra,
                    ty,
                    value_default,
                    ..
                } = &field.ty
                {
                    let extra = extra.convert();
                    let var = field.variable_ident();
                    let value_default = match value_default {
                        Some(e) => quote! { ::core::option::Option::Some(#e) },
                        None => quote! { ::core::option::Option::None },
                    };
                    let field = quote! {
                        ::bauble::types::FieldType {
                            id: registry.get_or_register_type::<#ty, #allocator>(),
                            extra: #extra,
                            default: #value_default,
                        }
                    };

                    if let Some(default) = default {
                        optional_fields.push(field);
                        let v = from_bauble(quote!(__val));
                        field_constructors.push(quote! {
                            let #var = __seq.next().map(|__val| #v).transpose()?.unwrap_or_else(|| #default);
                        });
                    } else {
                        required_fields.push(field);
                        let next = quote! { __seq.next().ok_or_else(|| {
                            Self::error(__span, ::bauble::ToRustErrorKind::WrongTupleLength {
                                found: __len,
                                expected: __expected_len,
                            })
                        })? };
                        let v = from_bauble(next);
                        field_constructors.push(quote! {
                            let #var = #v?;
                        });
                    }
                }
            }

            let expected_len = required_fields.len();
            let mut fields = quote! { ::bauble::types::UnnamedFields::empty() };
            if !required_fields.is_empty() {
                fields = quote! {
                    #fields
                        .with_required([#(#required_fields),*])
                };
            };

            if !optional_fields.is_empty() {
                fields = quote! {
                    #fields
                        .with_optional([#(#optional_fields),*])
                };
            };

            (
                Some((
                    if flatten {
                        quote! {
                            ::bauble::Value::Tuple(__seq)
                        }
                    } else {
                        quote! {
                            ::bauble::Value::Struct(::bauble::FieldsKind::Unnamed(__seq))
                        }
                    },
                    quote! {
                        {
                            let __len = __seq.len();
                            let __expected_len = #expected_len;
                            let mut __seq = __seq.into_iter();

                            #(#field_constructors)*

                            #construct
                        }
                    },
                )),
                if flatten {
                    quote! { ::bauble::types::TypeKind::Tuple(#fields) }
                } else {
                    quote! { ::bauble::types::TypeKind::Struct(::bauble::types::Fields::Unnamed(#fields)) }
                },
            )
        }
        (Some(FieldsKind::Named), false) => {
            let mut required_fields = Vec::new();
            let mut optional_fields = Vec::new();
            let mut field_constructors = Vec::new();
            for field in &fields.fields {
                if let FieldTy::Val {
                    default,
                    attribute: None,
                    extra,
                    ty,
                    value_default,
                    ..
                } = &field.ty
                {
                    let extra = extra.convert();
                    let var = field.variable_ident();
                    let name = field.name.to_string();
                    let value_default = match value_default {
                        Some(e) => quote! { ::core::option::Option::Some(#e) },
                        None => quote! { ::core::option::Option::None },
                    };
                    let field = quote! {
                        (
                            #name,
                            ::bauble::types::FieldType {
                                id: registry.get_or_register_type::<#ty, #allocator>(),
                                extra: #extra,
                                default: #value_default,
                            },
                        )
                    };

                    if let Some(default) = default {
                        optional_fields.push(field);
                        let v = from_bauble(quote!(__val));
                        field_constructors.push(quote! {
                            let #var = __fields.swap_remove(#name).map(|__val| #v).transpose()?.unwrap_or_else(|| #default);
                        });
                    } else {
                        required_fields.push(field);
                        let next = quote! { __fields.swap_remove(#name).ok_or_else(|| {
                            Self::error(__span, ::bauble::ToRustErrorKind::MissingField {
                                field: ::std::borrow::ToOwned::to_owned(#name),
                            })
                        })? };
                        let v = from_bauble(next);
                        field_constructors.push(quote! {
                            let #var = #v?;
                        });
                    }
                }
            }

            let mut fields = quote! { ::bauble::types::NamedFields::empty() };
            if !required_fields.is_empty() {
                fields = quote! {
                    #fields
                        .with_required([#(#required_fields),*])
                };
            };

            if !optional_fields.is_empty() {
                fields = quote! {
                    #fields
                        .with_optional([#(#optional_fields),*])
                };
            };

            (
                Some((
                    quote! {
                        ::bauble::Value::Struct(::bauble::FieldsKind::Named(mut __fields))
                    },
                    quote! {
                        {
                            #(#field_constructors)*

                            #construct
                        }
                    },
                )),
                quote! { ::bauble::types::TypeKind::Struct(::bauble::types::Fields::Named(#fields)) },
            )
        }
        (Some(FieldsKind::Named), true) => (
            None,
            Error::new(
                ty_info.span,
                "Flattening more than one named field isn't allowed.",
            )
            .into_compile_error(),
        ),
    }
}

/// Generate code to deserialize a struct or variant.
fn derive_struct(
    ty_info: TypeInfo,
    fields: &FieldsInfo,
    flatten: bool,
    from: Option<Type>,
) -> (TokenStream, TokenStream, TokenStream) {
    let allocator = &ty_info.allocator;
    let type_attributes = {
        let mut required = Vec::new();
        let mut optional = Vec::new();

        for field in &fields.fields {
            if let FieldTy::Val {
                attribute: Some(ident),
                ty,
                default,
                extra,
                value_default,
                ..
            } = &field.ty
            {
                let ident = ident.to_string();
                let extra = extra.convert();
                let value_default = match value_default {
                    Some(e) => quote! { ::core::option::Option::Some(#e) },
                    None => quote! { ::core::option::Option::None },
                };
                let attribute_field = quote! {
                    (#ident, ::bauble::types::FieldType {
                        id: registry.get_or_register_type::<#ty, #allocator>(),
                        extra: #extra,
                        default: #value_default,
                    })
                };

                if default.is_some() {
                    optional.push(attribute_field);
                } else {
                    required.push(attribute_field);
                }
            }
        }

        let mut fields = quote! {
            ::bauble::types::NamedFields::empty()
        };

        if !required.is_empty() {
            fields = quote! {
                #fields
                    .with_required([#(#required),*])
            };
        };

        if !optional.is_empty() {
            fields = quote! {
                #fields
                    .with_optional([#(#optional),*])
            };
        };

        fields
    };

    let ty = &ty_info.ty;
    let construct = match fields.real_kind {
        Some(_) => {
            let mut field_constructors = Vec::new();
            for field in &fields.fields {
                let ident = &field.name;

                let construct = match &field.ty {
                    FieldTy::Val {
                        default, attribute, ..
                    } => {
                        if let Some(attr) = attribute {
                            let ident = attr.to_string();
                            if let Some(default) = default {
                                let v = from_bauble(quote! { __val });
                                quote! {
                                    __attributes.take(#ident).map(|__val| #v).transpose()?.unwrap_or_else(|| #default)
                                }
                            } else {
                                let v = from_bauble(quote! {
                                    __attributes.take(#ident).ok_or_else(|| {
                                        Self::error(__span, ::bauble::ToRustErrorKind::MissingAttribute {
                                            attribute: ::std::borrow::ToOwned::to_owned(#ident),
                                            attributes_span: __attributes_span,
                                        })
                                    })?
                                });
                                quote! {
                                    #v?
                                }
                            }
                        } else {
                            let var = field.variable_ident();
                            quote! {
                                #var
                            }
                        }
                    }
                    FieldTy::AsDefault { default, .. } => default.clone(),
                };

                field_constructors.push(quote! {
                    #ident: #construct
                });
            }
            let ty = &ty_info.ty;
            quote! {
                #ty {
                    #(#field_constructors),*
                }
            }
        }
        None => {
            quote! { #ty }
        }
    };

    let (pattern, type_data) = match from {
        Some(from) => {
            let v = from_bauble(quote!(*__inner));
            let fields = fields.fields.iter().map(|f| {
                let ident = &f.name;
                let name = f.variable_ident();
                quote! { #ident: #name }
            });
            (
                Some((
                    quote! { ::bauble::Value::Transparent(__inner) },
                    quote! {{
                        let __from: #from = #v?;
                        let #ty {
                            #(#fields),*
                        } = ::std::convert::From::from(__from);

                        #construct
                    }},
                )),
                quote! { ::bauble::types::TypeKind::Transparent(registry.get_or_register_type::<#from, #allocator>()) },
            )
        }
        None => derive_fields(&ty_info, fields, &construct, flatten),
    };

    let construct = match pattern {
        Some((pattern, arm)) => {
            quote! {
                match __value {
                    #pattern => #arm,
                    _ => Err(Self::error(__span, ::bauble::ToRustErrorKind::WrongType { found: __ty }))?,
                }
            }
        }
        None => construct,
    };

    (type_attributes, type_data, construct)
}

fn derive_variants_from<'a>(
    variants: impl IntoIterator<Item = &'a syn::Variant>,
    flatten: bool,
    allocator: TokenStream,
    default: fn(TokenStream) -> TokenStream,
    from: Type,
) -> syn::Result<(TokenStream, TokenStream, TokenStream)> {
    for variant in variants.into_iter() {
        let variant_attrs = ContainerAttrs::parse(
            &variant.attrs,
            ContainerType::Container,
            flatten,
            Some(from.clone()),
            default,
        )?;

        let fields = parse_fields(&variant.fields, variant_attrs.tuple, true, default)?;

        for field in fields.fields {
            if !matches!(field.ty, FieldTy::Val {
                    default: None,
                    attribute: None,
                    extra,
                    ..
                } if extra.0.is_empty())
            {
                Err(syn::Error::new(
                    field.name.span(),
                    "Can't have attributes on fields in an enum with the `from` attribute",
                ))?
            }
        }
    }

    let v = from_bauble(quote!(*__inner));

    Ok((
        quote! { ::bauble::types::NamedFields::empty() },
        quote! { ::bauble::types::TypeKind::Transparent(registry.get_or_register_type::<#from, #allocator>()) },
        quote! {
            match __value {
                ::bauble::Value::Transparent(__inner) => {
                    let __from: #from = #v?;
                    let __res: Self = ::std::convert::From::from(__from);

                    __res
                },
                _ => Err(Self::error(__span, ::bauble::ToRustErrorKind::WrongType {
                    found: __ty,
                }))?,
            }
        },
    ))
}

fn derive_variants<'a>(
    variants: impl IntoIterator<Item = &'a syn::Variant>,
    flatten: bool,
    allocator: TokenStream,
    default: fn(TokenStream) -> TokenStream,
) -> syn::Result<(TokenStream, TokenStream, TokenStream)> {
    let mut type_variants = Vec::new();
    let mut match_construct = Vec::new();
    for variant in variants.into_iter() {
        let variant_attrs = ContainerAttrs::parse(
            &variant.attrs,
            ContainerType::Container,
            flatten,
            None,
            default,
        )?;

        let ident = variant.ident.clone();
        let name = variant_attrs
            .rename
            .map(|s| s.to_string())
            .unwrap_or(ident.to_string());

        let fields = parse_fields(&variant.fields, variant_attrs.tuple, false, default)?;

        let (type_attrs, type_kind, construct_variant) = derive_struct(
            TypeInfo {
                span: variant.span(),
                ty: quote! { Self::#ident },
                allocator: allocator.clone(),
            },
            &fields,
            variant_attrs.flatten,
            None,
        );

        let extra = variant_attrs.extra.convert();
        let validate = variant_attrs.validate.into_iter();
        let default = variant_attrs.value_default.into_iter();
        type_variants.push(quote! {
            ::bauble::types::Variant::flattened(::bauble::path::TypePathElem::new(#name).unwrap(), #type_kind)
                .with_attributes(#type_attrs)
                .with_extra(#extra)
                #(.with_default(#default))*
                #(.with_validation(#validate))*
        });

        match_construct.push(quote! {
            #name => {
                #construct_variant
            }
        });
    }

    Ok((
        // The outer enum doesn't have any attributes.
        quote! { ::bauble::types::NamedFields::empty() },
        quote! {
            {
                let variants = [#(#type_variants),*];
                ::bauble::types::TypeKind::Enum { variants: registry.build_enum(variants) }
            }
        },
        quote! {
            match __value {
                ::bauble::Value::Enum(__variant, __value) => {
                    let ::bauble::Val {
                        attributes: ::bauble::Spanned {
                            value: mut __attributes,
                            span: __attributes_span,
                        },
                        value: ::bauble::Spanned { span: __span, value: __value },
                        ty: __ty,
                    } = *__value;

                    match __variant.as_str() {
                        #(
                            #match_construct
                        )*

                        _ => Err(Self::error(__span, ::bauble::ToRustErrorKind::UnknownVariant {
                            variant: ::bauble::Spanned::new(__variant.span, ::std::borrow::ToOwned::to_owned(__variant.as_str())),
                        }))?
                    }
                },
                _ => Err(Self::error(__span, ::bauble::ToRustErrorKind::WrongType {
                    found: __ty,
                }))?,
            }
        },
    ))
}

pub fn derive_bauble_derive_input(
    ast: &DeriveInput,
    allocator: Option<TokenStream>,
    default: Option<fn(TokenStream) -> TokenStream>,
    mut traits: Vec<TokenStream>,
) -> TokenStream {
    let default = default.unwrap_or(|ty| quote! { <#ty as ::core::default::Default>::default() });
    let ty_attrs = match ContainerAttrs::parse(
        &ast.attrs,
        match ast.data {
            Data::Struct(_) => ContainerType::Both,
            Data::Enum(_) => ContainerType::Type,
            Data::Union(_) => ContainerType::Both,
        },
        false,
        None,
        default,
    ) {
        Ok(a) => a,
        Err(e) => return e.into_compile_error(),
    };

    traits.extend(ty_attrs.traits);

    let allocator = ty_attrs
        .allocator
        .or(allocator)
        .unwrap_or_else(|| quote! { ::bauble::DefaultAllocator });

    let (_, ty_generics, where_clause) = ast.generics.split_for_impl();
    let mut where_clause = where_clause.cloned().unwrap_or_else(|| WhereClause {
        where_token: Default::default(),
        predicates: Default::default(),
    });
    if let Some(bounds) = ty_attrs.bounds {
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
    let name = ty_attrs.rename.as_ref().unwrap_or(ident);

    let path = match ty_attrs.path {
        Some(path) => {
            quote! { #path }
        }
        None => quote! { module_path!() },
    };

    let name_str = name.to_string();
    let generic_path =
        quote! { ::bauble::path::TypePath::new(format!("{}::{}", #path, #name_str)).unwrap() };

    let has_generics = generics.params.len() > 1;

    let generic_type = if has_generics {
        quote! {  Some(registry.get_or_register_generic_type(__generic_path)) }
    } else {
        quote! { None }
    };

    let generic_types = generics
        .params
        .iter()
        .filter_map(|generic| match generic {
            syn::GenericParam::Type(type_param) => {
                let ident = &type_param.ident;
                Some(quote! {
                    let __inner_ty = registry.get_or_register_type::<#ident, #allocator>();
                    s.push_str(registry.key_type(__inner_ty).meta.path.as_str());
                })
            }
            _ => None,
        })
        .reduce(|a, b| {
            quote! {
                #a
                s.push_str(", ");
                #b
            }
        });

    let type_path = if let Some(types) = generic_types {
        quote! {
            ::bauble::path::TypePath::new({
                let mut s = __generic_path.to_string();
                #types
                s
            }).unwrap()
        }
    } else {
        quote! { __generic_path }
    };

    // Generate code to deserialize this type
    let (type_attributes, construct_type, construct_value) = match &ast.data {
        Data::Struct(data) => {
            let fields = match parse_fields(
                &data.fields,
                ty_attrs.tuple,
                ty_attrs.from.is_some(),
                default,
            ) {
                Ok(fields) => fields,
                Err(err) => return err.into_compile_error(),
            };

            let ty = quote! { Self };
            derive_struct(
                TypeInfo {
                    span: data.fields.span(),
                    ty,
                    allocator: allocator.clone(),
                },
                &fields,
                ty_attrs.flatten,
                ty_attrs.from,
            )
        }
        Data::Enum(data) => {
            if data.variants.is_empty() {
                return Error::new(
                    data.enum_token.span,
                    "Can't derive `Bauble` on an empty enum",
                )
                .into_compile_error();
            }
            match match ty_attrs.from {
                Some(from) => derive_variants_from(
                    &data.variants,
                    ty_attrs.flatten,
                    allocator.clone(),
                    default,
                    from,
                ),
                None => {
                    derive_variants(&data.variants, ty_attrs.flatten, allocator.clone(), default)
                }
            } {
                Ok(res) => res,
                Err(e) => return e.into_compile_error(),
            }
        }
        Data::Union(data) => {
            return Error::new_spanned(data.union_token, "unions are not supported")
                .to_compile_error();
        }
    };

    let extra = ty_attrs.extra.convert();

    let extra_validation = ty_attrs
        .validate
        .map(|v| quote!(::core::option::Option::Some(#v)))
        .unwrap_or(quote!(::core::option::Option::None));

    let default = match ty_attrs.value_default {
        Some(e) => quote! { ::core::option::Option::Some(#e) },
        None => quote! { ::core::option::Option::None },
    };

    let nullable_bool = ty_attrs.nullable.is_some();
    let nullable_expr = ty_attrs.nullable.map(|e| {
        quote! {
            if let ::bauble::Value::Primitive(::bauble::PrimitiveValue::Null) = &__value {
                return Ok((#e)(__allocator));
            }
        }
    });

    // Assemble the implementation
    quote! {
        #[automatically_derived]
        impl #modified_impl_generics ::bauble::Bauble<#lifetime, #allocator>
            for #ident #ty_generics
            #where_clause
        {
            fn construct_type(registry: &mut ::bauble::types::TypeRegistry) -> ::bauble::types::Type {
                let __generic_path = #generic_path;
                let __path = #type_path;

                ::bauble::types::Type {
                    meta: ::bauble::types::TypeMeta {
                        path: __path,
                        generic_base_type: #generic_type,
                        extra: #extra,
                        attributes: #type_attributes,
                        default: #default,
                        nullable: #nullable_bool,
                        traits: ::std::vec![#(registry.get_or_register_trait::<dyn #traits>()),*],
                        extra_validation: #extra_validation,
                    },
                    kind: #construct_type,
                }
            }

            fn from_bauble(
                ::bauble::Val {
                    attributes: ::bauble::Spanned {
                        value: mut __attributes,
                        span: __attributes_span,
                    },
                    value: ::bauble::Spanned { span: __span, value: __value },
                    ty: __ty,
                }: ::bauble::Val,
                __allocator: &#allocator,
            ) -> ::std::result::Result<
                <#allocator as ::bauble::BaubleAllocator<#lifetime>>::Out<Self>,
                ::bauble::ToRustError,
            > {
                #nullable_expr

                let res = #construct_value;

                // SAFETY: We only use this allocator when  constructing values.
                Ok(unsafe { ::bauble::BaubleAllocator::wrap(__allocator, res) })
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

    derive_bauble_derive_input(&ast, None, None, Vec::new())
}
