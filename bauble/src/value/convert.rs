use crate::{
    ConversionError, FieldsKind, PrimitiveValue, Span,
    parse::{ParseVal, Path},
    path::{TypePath, TypePathElem},
    spanned::{SpanExt, Spanned},
    types::{self, TypeId},
    value::Fields,
};

use super::{Attributes, CopyVal, Ident, Result, Symbols, Val, Value};

pub fn no_attr() -> Option<&'static Attributes<Val>> {
    None
}

fn set_attributes<C: ConvertValue, F: FnMut(TypePathElem<&str>, Val, &Symbols) -> Result<Value>>(
    mut val: Val,
    attributes: &Attributes<C>,
    mut meta: ConvertMeta<F>,
) -> Result<Val> {
    let types = meta.symbols.ctx.type_registry();
    let ty = types.key_type(val.ty.value);

    for (ident, value) in attributes.iter() {
        let Some(ty) = ty.meta.attributes.get(ident.as_str()) else {
            return Err(ConversionError::UnexpectedField {
                attribute: true,
                field: ident.clone(),
                ty: val.ty.value,
            }
            .spanned(ident.span));
        };

        if let Some((first, _)) = val.attributes.get(ident.as_str()) {
            return Err(ConversionError::DuplicateAttribute {
                first: first.clone(),
                second: ident.clone(),
            }
            .spanned(ident.span));
        }

        let value = value.convert(meta.reborrow(), ty.id, no_attr())?;

        val.attributes.insert(ident.clone(), value);
    }

    Ok(val)
}

fn resolve_type(
    symbols: &Symbols,
    expected_type: TypeId,
    val_type: &mut Option<Spanned<TypeId>>,
    primitive_type: Option<types::Primitive>,
    span: crate::Span,
) -> Result<Spanned<TypeId>> {
    let types = symbols.ctx.type_registry();
    let ty = if types.key_type(expected_type).kind.instanciable() {
        expected_type.spanned(val_type.map(|s| s.span).unwrap_or(span))
    } else {
        match default_value_type(symbols, primitive_type, *val_type) {
            Some(ty) => {
                let ty = ty.spanned(val_type.map_or(span, |s| s.span));
                *val_type = Some(ty);

                ty
            }
            None => {
                return Err(ConversionError::ExpectedExactType {
                    expected: expected_type,
                    got: None,
                }
                .spanned(span));
            }
        }
    };

    if let Some(val_type) = val_type {
        if !types.can_infer_from(expected_type, val_type.value) {
            return Err(ConversionError::ExpectedExactType {
                expected: expected_type,
                got: Some(val_type.value),
            }
            .spanned(span));
        }
    }

    Ok(ty)
}

pub(super) fn value_type(value: &ParseVal, symbols: &Symbols) -> Result<Option<Spanned<TypeId>>> {
    let types = symbols.ctx.type_registry();

    if let Some(ty) = &value.ty {
        return Ok(Some(symbols.resolve_type(ty)?.spanned(ty.span())));
    };

    let ty = match &value.value.value {
        Value::Ref(path) => {
            // Don't resolve types of copy types.
            if let Some(ident) = path.as_ident()
                && symbols.try_resolve_copy(&ident).is_some()
            {
                None
            } else {
                Some(symbols.resolve_asset(path)?.0.spanned(path.span()))
            }
        }
        Value::Or(paths) => {
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

                            if !matches!(enum_ty.kind, types::TypeKind::Or { .. }) {
                                // This could've been an enum too.
                                return Err(ConversionError::ExpectedBitfield { got: *enum_type }
                                    .spanned(path.span()));
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
                                .spanned(path.span()))
                        }
                    }
                    _ => {
                        Err(ConversionError::ExpectedBitfield { got: variant_ty }
                            .spanned(path.span()))
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
                            .spanned(path.span()));
                        }
                    }
                    None => ty = Some(enum_type),
                }
            }

            ty.map(|t| t.spanned(value.value.span))
        }
        Value::Transparent(inner) | Value::Enum(_, inner) => value_type(inner, symbols)?,
        Value::Tuple(_)
        | Value::Map(_)
        | Value::Array(_)
        | Value::Struct(_)
        | Value::Primitive(_) => None,
    };

    Ok(ty)
}
pub(super) fn default_value_type(
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

#[derive(Clone, Copy, Debug)]
pub(super) enum AnyVal<'a> {
    Parse(&'a ParseVal),
    Copy(&'a CopyVal),
    Complete(&'a Val),
}

pub struct ConvertMeta<'a, F> {
    pub symbols: &'a Symbols<'a>,
    pub add_value: &'a mut F,
    pub object_name: TypePathElem<&'a str>,
}

impl<F> ConvertMeta<'_, F> {
    pub fn reborrow(&mut self) -> ConvertMeta<F> {
        ConvertMeta {
            symbols: self.symbols,
            add_value: self.add_value,
            object_name: self.object_name,
        }
    }

    fn with_object_name<'b>(&'b mut self, name: TypePathElem<&'b str>) -> ConvertMeta<'b, F> {
        ConvertMeta {
            symbols: self.symbols,
            add_value: self.add_value,
            object_name: name,
        }
    }
}

/// This trait has an implementation to convert any `Value` into a finished `Val`.
trait ConvertValueInner: ConvertValue {
    type Ref: std::fmt::Debug;
    type Variant: std::fmt::Debug;

    fn variant_span(variant: &Self::Variant) -> Span;

    fn get_variant(ident: &Self::Variant, symbols: &Symbols) -> Result<TypePathElem>;

    fn get_asset(ident: &Self::Ref, symbols: &Symbols) -> Result<TypePath>;

    fn ref_ident(path: &Self::Ref) -> Option<TypePathElem<&str>>;

    fn convert_inner<
        'a,
        C: ConvertValue,
        F: FnMut(TypePathElem<&str>, Val, &Symbols) -> Result<Value>,
    >(
        value: &Spanned<Value<Self, Self::Ref, Self::Variant>>,
        attributes: &Spanned<Attributes<Self>>,
        val_ty: Option<Spanned<TypeId>>,
        mut meta: ConvertMeta<'a, F>,
        expected_type: TypeId,
        extra_attributes: Option<&'a Attributes<C>>,
    ) -> Result<Val> {
        // Resolve copy refs.
        if let Value::Ref(r) = &value.value
            && let Some(ident) = Self::ref_ident(r)
            && let Some((copy, Some(val))) = meta.symbols.try_resolve_copy(ident.as_str())
        {
            return match extra_attributes {
                Some(s) if !s.0.is_empty() => {
                    let mut extra = ConvertValue::to_any_attributes(s);

                    for (i, v) in attributes.iter() {
                        if let Some((ident, _)) = extra.0.get_key_value(i.as_str()) {
                            Err(ConversionError::DuplicateAttribute {
                                first: ident.clone(),
                                second: i.clone(),
                            }
                            .spanned(i.span))?
                        }

                        extra.0.insert(i.clone(), v.to_any());
                    }

                    val.convert(meta.reborrow(), expected_type, Some(&extra))
                }
                _ => val.convert(
                    meta.reborrow(),
                    expected_type,
                    if attributes.is_empty() {
                        None
                    } else {
                        Some(&attributes.value)
                    },
                ),
            }
            .map_err(|err| {
                ConversionError::ErrorInCopy {
                    copy: copy.to_owned().spanned(val.span()),
                    error: Box::new(err),
                }
                .spanned(value.span)
            });
        }

        let raw_val_type = val_ty;
        let mut val_ty = val_ty;

        let ty_id = resolve_type(
            meta.symbols,
            expected_type,
            &mut val_ty,
            value.value.primitive_type(),
            value.span,
        )?;

        let types = meta.symbols.ctx.type_registry();
        let ty = types.key_type(ty_id.value);

        let span = value.span;
        let expected_err = || {
            ConversionError::ExpectedExactType {
                expected: expected_type,
                got: val_ty.map(|s| s.value),
            }
            .spanned(ty_id.span)
        };

        if !ty.kind.instanciable() {
            Err(expected_err())?
        }

        /// Macro to parse unnamed fields.
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

                let l = values.len();
                for value in values {
                    let (_, ty) = types.next().ok_or_else(|| {
                        // input tuple too long.
                        ConversionError::WrongLength { got: l, ty: *ty_id }.spanned(value.span())
                    })?;

                    seq.push(value.convert(meta.reborrow(), ty, no_attr())?);
                }

                seq
            }};
        }

        /// A struct to store extra attributes, this is mostly to avoid allocations in most cases.
        enum ExtraAttributes<'a, C0, C1> {
            None,
            BorrowedA(&'a Attributes<C0>),
            BorrowedB(&'a Attributes<C1>),
            BorrowedC(&'a Attributes<Val>),
            Owned(Attributes<AnyVal<'a>>),
        }

        impl<'a, C0: ConvertValue, C1: ConvertValue> ExtraAttributes<'a, C0, C1> {
            fn get_mut(&mut self) -> &mut Attributes<AnyVal<'a>> {
                match self {
                    ExtraAttributes::None => {
                        *self = ExtraAttributes::Owned(Attributes::default());

                        self.get_mut()
                    }
                    ExtraAttributes::BorrowedA(attributes) => {
                        *self = ExtraAttributes::Owned(C0::to_any_attributes(attributes));

                        self.get_mut()
                    }
                    ExtraAttributes::BorrowedB(attributes) => {
                        *self = ExtraAttributes::Owned(C1::to_any_attributes(attributes));

                        self.get_mut()
                    }
                    ExtraAttributes::BorrowedC(attributes) => {
                        *self = ExtraAttributes::Owned(Val::to_any_attributes(attributes));

                        self.get_mut()
                    }
                    ExtraAttributes::Owned(attributes) => attributes,
                }
            }

            pub fn extend(&mut self, attributes: &'a Attributes<Val>) {
                if self.is_empty() {
                    *self = ExtraAttributes::BorrowedC(attributes);
                } else {
                    self.get_mut().0.extend(
                        attributes
                            .iter()
                            .map(|(ident, v)| (ident.clone(), v.to_any())),
                    );
                }
            }

            fn convert_with<F_: FnMut(TypePathElem<&str>, Val, &Symbols) -> Result<Value>>(
                &mut self,
                value: &C1,
                meta: ConvertMeta<F_>,
                expected_type: TypeId,
            ) -> Result<Val> {
                match std::mem::replace(self, ExtraAttributes::None) {
                    ExtraAttributes::None => value.convert(meta, expected_type, no_attr()),
                    ExtraAttributes::BorrowedA(attributes) => {
                        value.convert(meta, expected_type, Some(attributes))
                    }
                    ExtraAttributes::BorrowedB(attributes) => {
                        value.convert(meta, expected_type, Some(attributes))
                    }
                    ExtraAttributes::BorrowedC(attributes) => {
                        value.convert(meta, expected_type, Some(attributes))
                    }
                    ExtraAttributes::Owned(attributes) => {
                        value.convert(meta, expected_type, Some(&attributes))
                    }
                }
            }

            fn convert_inner_with<F_: FnMut(TypePathElem<&str>, Val, &Symbols) -> Result<Value>>(
                &mut self,
                value: &Spanned<Value<C1, C1::Ref, C1::Variant>>,
                attributes: &Spanned<Attributes<C1>>,
                val_ty: Option<Spanned<TypeId>>,
                meta: ConvertMeta<F_>,
                expected_type: TypeId,
            ) -> Result<Val>
            where
                C1: ConvertValueInner,
            {
                match std::mem::replace(self, ExtraAttributes::None) {
                    ExtraAttributes::None => {
                        C1::convert_inner(value, attributes, val_ty, meta, expected_type, no_attr())
                    }
                    ExtraAttributes::BorrowedA(extra_attributes) => C1::convert_inner(
                        value,
                        attributes,
                        val_ty,
                        meta,
                        expected_type,
                        Some(extra_attributes),
                    ),
                    ExtraAttributes::BorrowedB(extra_attributes) => C1::convert_inner(
                        value,
                        attributes,
                        val_ty,
                        meta,
                        expected_type,
                        Some(extra_attributes),
                    ),
                    ExtraAttributes::BorrowedC(extra_attributes) => C1::convert_inner(
                        value,
                        attributes,
                        val_ty,
                        meta,
                        expected_type,
                        Some(extra_attributes),
                    ),
                    ExtraAttributes::Owned(extra_attributes) => C1::convert_inner(
                        value,
                        attributes,
                        val_ty,
                        meta,
                        expected_type,
                        Some(&extra_attributes),
                    ),
                }
            }

            fn is_empty(&self) -> bool {
                match self {
                    ExtraAttributes::None => true,
                    ExtraAttributes::BorrowedA(a) => a.is_empty(),
                    ExtraAttributes::BorrowedB(a) => a.is_empty(),
                    ExtraAttributes::BorrowedC(a) => a.is_empty(),
                    ExtraAttributes::Owned(a) => a.is_empty(),
                }
            }

            fn first(&self) -> Option<&Ident> {
                match self {
                    ExtraAttributes::None => None,
                    ExtraAttributes::BorrowedA(attributes) => attributes.first().map(|(k, _)| k),
                    ExtraAttributes::BorrowedB(attributes) => attributes.first().map(|(k, _)| k),
                    ExtraAttributes::BorrowedC(attributes) => attributes.first().map(|(k, _)| k),
                    ExtraAttributes::Owned(attributes) => attributes.first().map(|(k, _)| k),
                }
            }
        }

        let attributes_span = attributes.span;

        let (attributes, mut extra_attributes) = {
            let object_name =
                TypePathElem::new(format!("{}#", meta.object_name)).expect("No :: were added");
            let mut meta = meta.with_object_name(object_name.borrow());

            let mut new_attrs = Attributes::default();
            // We prioritise taking from `extra_attributes`. Putting extra stuff in a new `extra_attributes`.
            let mut extra_attributes = if let Some(extra_attributes) = extra_attributes {
                for (ident, v) in extra_attributes {
                    let Some(ty) = ty.meta.attributes.get(ident.as_str()) else {
                        continue;
                    };

                    new_attrs.insert(ident.clone(), v.convert(meta.reborrow(), ty.id, no_attr())?);
                }

                if new_attrs.is_empty() {
                    // All of the extra attributes left.
                    ExtraAttributes::BorrowedA(extra_attributes)
                } else if new_attrs.len() == extra_attributes.len() {
                    // None of the extra attributes left.
                    ExtraAttributes::None
                } else {
                    // Part of the extra attributes left.
                    ExtraAttributes::Owned(Attributes(
                        extra_attributes
                            .iter()
                            .filter(|(i, _)| new_attrs.get(i.as_str()).is_none())
                            .map(|(i, v)| (i.clone(), v.to_any()))
                            .collect(),
                    ))
                }
            } else {
                ExtraAttributes::None
            };

            let old_len = new_attrs.len();
            let empty = extra_attributes.is_empty();
            // And then we take from our own attributes, putting duplicates and extra stuff in `extra_attributes`.
            for (ident, v) in &attributes.value {
                let (Some(ty), false) = (
                    ty.meta.attributes.get(ident.as_str()),
                    new_attrs.get(ident.as_str()).is_some(),
                ) else {
                    if !empty {
                        let extra = extra_attributes.get_mut();
                        if let Some((first, _)) = extra.get(ident.as_str()) {
                            Err(ConversionError::DuplicateAttribute {
                                first: first.clone(),
                                second: ident.clone(),
                            }
                            .spanned(ident.span))?
                        }

                        extra.insert(ident.clone(), v.to_any());
                    }
                    continue;
                };
                // We checked that `new_attributes` didn't contain this field.
                new_attrs.insert(ident.clone(), v.convert(meta.reborrow(), ty.id, no_attr())?);
            }

            if empty {
                extra_attributes = if new_attrs.len() == old_len {
                    // All of the extra attributes left.
                    ExtraAttributes::BorrowedB(&attributes.value)
                } else if new_attrs.len() == old_len + attributes.len() {
                    // None of the extra attributes left.
                    ExtraAttributes::None
                } else {
                    // Part of the extra attributes left.
                    ExtraAttributes::Owned(Attributes(
                        attributes
                            .iter()
                            .filter(|(i, _)| new_attrs.get(i.as_str()).is_none())
                            .map(|(i, v)| (i.clone(), v.to_any()))
                            .collect(),
                    ))
                }
            }

            // Check if we're missing any required attributes.
            for (attr, _) in ty.meta.attributes.required.iter() {
                if new_attrs.get(attr.as_str()).is_none() {
                    return Err(ConversionError::MissingField {
                        attribute: true,
                        field: attr.clone(),
                        ty: ty_id.value,
                    }
                    .spanned(attributes_span));
                }
            }

            (new_attrs, extra_attributes)
        };

        let value = match (&ty.kind, &value.value) {
            (types::TypeKind::Tuple(fields), Value::Tuple(values)) => {
                Value::Tuple(parse_unnamed!(fields, values))
            }
            (types::TypeKind::Array(array_type), Value::Array(arr)) => {
                if array_type
                    .len
                    .is_some_and(|expected_len| expected_len != arr.len())
                {
                    Err(ConversionError::WrongLength {
                        got: arr.len(),
                        ty: *ty_id,
                    }
                    .spanned(span))?
                }

                let mut values = Vec::with_capacity(arr.len());

                for value in arr {
                    values.push(value.convert(meta.reborrow(), array_type.ty.id, no_attr())?);
                }

                Value::Array(values)
            }
            (types::TypeKind::Map(map_type), Value::Map(map)) => {
                if map_type
                    .len
                    .is_some_and(|expected_len| expected_len != map.len())
                {
                    Err(ConversionError::WrongLength {
                        got: map.len(),
                        ty: *ty_id,
                    }
                    .spanned(span))?
                }

                let mut values = Vec::with_capacity(map.len());

                for (key, value) in map {
                    values.push((
                        key.convert(meta.reborrow(), map_type.key.id, no_attr())?,
                        value.convert(meta.reborrow(), map_type.value.id, no_attr())?,
                    ));
                }

                Value::Map(values)
            }
            // Both struct and enum variant are parsed from a `Struct` value.
            (
                types::TypeKind::Struct(fields) | types::TypeKind::EnumVariant { fields, .. },
                Value::Struct(f),
            ) => Value::Struct(match (fields, f) {
                (types::Fields::Unit, FieldsKind::Unit) => FieldsKind::Unit,
                (types::Fields::Unnamed(fields), FieldsKind::Unnamed(values)) => {
                    FieldsKind::Unnamed(parse_unnamed!(fields, values))
                }
                (types::Fields::Named(fields), FieldsKind::Named(value_fields)) => {
                    for (field, _) in fields.required.iter() {
                        if !value_fields.contains_key(field.as_str()) {
                            Err(ConversionError::MissingField {
                                attribute: false,
                                field: field.clone(),
                                ty: *ty_id,
                            }
                            .spanned(span))?
                        }
                    }

                    let mut new_fields = Fields::with_capacity(value_fields.len());
                    for (field, value) in value_fields {
                        let Some(ty) = fields.get(field.as_str()) else {
                            Err(ConversionError::UnexpectedField {
                                attribute: false,
                                field: field.clone(),
                                ty: *ty_id,
                            }
                            .spanned(span))?
                        };

                        new_fields.insert(
                            field.clone(),
                            value.convert(meta.reborrow(), ty.id, no_attr())?,
                        );
                    }

                    FieldsKind::Named(new_fields)
                }
                _ => Err(ConversionError::WrongFields { ty: *ty_id }.spanned(span))?,
            }),
            (types::TypeKind::Enum { variants }, _) => {
                // First see if we already have the correct value.
                let (variant, inner) = if let Value::Enum(variant, value) = &value.value
                    && raw_val_type.is_some_and(|ty| ty.value == ty_id.value)
                {
                    let variant = Self::get_variant(variant, meta.symbols)?
                        .spanned(Self::variant_span(variant));
                    let ty = variants.get(variant.borrow()).ok_or(
                        ConversionError::UnknownVariant {
                            variant: variant.clone(),
                            ty: ty_id.value,
                        }
                        .spanned(span),
                    )?;
                    (
                        variant.map(|v| v.to_owned()),
                        extra_attributes.convert_with(value, meta.reborrow(), ty)?,
                    )
                }
                // Otherwise see if we have the value of an `EnumVariant` or its generic type.
                else if let Some(raw_val_type) = raw_val_type
                    && let Some((variant, variant_ty)) =
                        variants.iter().find(|(_, ty)| {
                            *ty == raw_val_type.value
                                || types.key_type(*ty).meta.generic_base_type.is_some_and(|t| {
                                    types.key_generic(t).contains(raw_val_type.value)
                                })
                        })
                {
                    (
                        variant.to_owned().spanned(raw_val_type.span),
                        extra_attributes.convert_inner_with(
                            value,
                            &Spanned::new(attributes_span, Default::default()),
                            Some(raw_val_type),
                            meta.reborrow(),
                            variant_ty,
                        )?,
                    )
                }
                // If not, try to parse as all different variants, we could still convert
                // correctly if we just did this step. But it produces ugly errors, and
                // isn't as easy to check as the other ways.
                else {
                    let mut variant_errors = Vec::new();

                    let (variant, inner) = variants
                        .iter()
                        .find_map(|(variant, ty)| {
                            Some((
                                variant,
                                extra_attributes
                                    .convert_inner_with(
                                        value,
                                        &Spanned::new(attributes_span, Default::default()),
                                        raw_val_type,
                                        meta.reborrow(),
                                        ty,
                                    )
                                    .map_err(|err| variant_errors.push((ty, Box::new(err))))
                                    .ok()?,
                            ))
                        })
                        .ok_or(
                            ConversionError::VariantErrors {
                                variant_errors,
                                ty: *ty_id,
                            }
                            .spanned(span),
                        )?;

                    (variant.to_owned().spanned(inner.span()), inner)
                };

                Value::Enum(variant, Box::new(inner))
            }
            // An or-type can be just one path, represented by a struct with unit fields.
            (types::TypeKind::Or(variants), Value::Struct(f)) => {
                if matches!(f, FieldsKind::Unit) {
                    if let Some(val_type) = raw_val_type {
                        match &types.key_type(val_type.value).kind {
                            types::TypeKind::EnumVariant {
                                variant,
                                enum_type,
                                fields,
                            } => {
                                debug_assert!(matches!(fields, types::Fields::Unit));
                                debug_assert_eq!(*enum_type, *ty_id);
                                debug_assert!(variants.variants.contains(variant));

                                Value::Or(vec![variant.clone().spanned(span)])
                            }

                            types::TypeKind::Generic(generic) => types
                                .iter_type_set(generic)
                                .next()
                                .map(|t| {
                                    if let types::TypeKind::EnumVariant { variant, .. } =
                                        &types.key_type(t).kind
                                    {
                                        Value::Or(vec![variant.clone().spanned(span)])
                                    } else {
                                        unreachable!(
                                            "Our type checking should make sure this can't happen"
                                        )
                                    }
                                })
                                .expect("Our type checking should make sure this can't happen"),

                            _ => Err(expected_err())?,
                        }
                    } else {
                        Err(expected_err())?
                    }
                } else {
                    Err(ConversionError::WrongFields { ty: *ty_id }.spanned(span))?
                }
            }
            // Or it can be the `Or` value. We assume this is correctly type because of the checks
            // for `Or` in `value_type`.
            (types::TypeKind::Or(_), Value::Or(idents)) => {
                let variants = idents
                    .iter()
                    .map(|ident| {
                        Ok(Self::get_variant(ident, meta.symbols)?
                            .to_owned()
                            .spanned(Self::variant_span(ident)))
                    })
                    .collect::<Result<_>>()?;

                Value::Or(variants)
            }
            // A ref can be from a ref value.
            (types::TypeKind::Ref(_), Value::Ref(r)) => {
                Value::Ref(Self::get_asset(r, meta.symbols)?)
            }
            // Or from another value, and we instantiate a new object that we can refer to.
            (types::TypeKind::Ref(ty), _) => {
                let object_name = TypePathElem::new(format!("{}&{}", meta.object_name, ty.inner()))
                    .expect("We didn't add any ::");
                let val = extra_attributes.convert_inner_with(
                    value,
                    &Spanned::new(attributes_span, Default::default()),
                    raw_val_type,
                    meta.with_object_name(object_name.borrow()),
                    *ty,
                )?;

                (meta.add_value)(object_name.borrow(), val, meta.symbols)?
            }
            (types::TypeKind::Primitive(primitive), Value::Primitive(value)) => {
                Value::Primitive(match (primitive, value) {
                    (types::Primitive::Num, PrimitiveValue::Num(v)) => PrimitiveValue::Num(*v),
                    (types::Primitive::Bool, PrimitiveValue::Bool(v)) => PrimitiveValue::Bool(*v),
                    (types::Primitive::Unit, PrimitiveValue::Unit) => PrimitiveValue::Unit,
                    (types::Primitive::Str, PrimitiveValue::Str(v)) => {
                        PrimitiveValue::Str(v.clone())
                    }
                    (types::Primitive::Raw, PrimitiveValue::Raw(v)) => {
                        PrimitiveValue::Raw(v.clone())
                    }

                    // NOTE: Keep this exhaustive so this can be found when adding a new primitive type.
                    (
                        types::Primitive::Num
                        | types::Primitive::Bool
                        | types::Primitive::Unit
                        | types::Primitive::Str
                        | types::Primitive::Raw
                        | types::Primitive::Any,
                        _,
                    ) => Err(expected_err())?,
                })
            }
            // Either we get a transparent value,
            (types::TypeKind::Transparent(ty), Value::Transparent(value)) => {
                let val = extra_attributes.convert_with(value, meta.reborrow(), *ty)?;

                Value::Transparent(Box::new(val))
            }
            // or we convert from a flat one.
            (types::TypeKind::Transparent(ty), _) => {
                let val = extra_attributes.convert_inner_with(
                    value,
                    &Spanned::new(attributes_span, Default::default()),
                    raw_val_type,
                    meta.reborrow(),
                    *ty,
                )?;

                Value::Transparent(Box::new(val))
            }
            (_, Value::Transparent(value)) => {
                // Try again as if it wasn't a transparent value.
                extra_attributes.extend(&attributes);
                return extra_attributes.convert_with(value, meta.reborrow(), expected_type);
            }
            _ => Err(expected_err())?,
        };

        // Report errors for unexpected attributes
        if let Some(ident) = extra_attributes.first() {
            Err(ConversionError::UnexpectedField {
                attribute: true,
                field: ident.clone(),
                ty: *ty_id,
            }
            .spanned(attributes_span))?;
        }

        let val = Val {
            ty: ty_id,
            value: value.spanned(span),
            attributes: attributes.spanned(attributes_span),
        };

        if let Some(validation) = ty.meta.extra_validation {
            validation(&val, types).map_err(|e| e.spanned(span))?
        }

        Ok(val)
    }
}

/// This trait is used to convert a certain bauble value to a fully resolved bauble value.
///
/// We do type resolution, validating etc here.
///
/// There are three stages of bauble values:
/// 1. `ParseVal`, which we get when we parse bauble from types.
/// 2. `CopyVal`, an intermediate value that we convert all copy values to.
/// 3. `Val`, the fully resolved type, which is always correct to convert to rust.
pub(super) trait ConvertValue: Clone + std::fmt::Debug {
    fn to_any(&self) -> AnyVal;

    fn to_any_attributes(attributes: &Attributes<Self>) -> Attributes<AnyVal<'_>> {
        Attributes(
            attributes
                .0
                .iter()
                .map(|(i, v)| (i.clone(), v.to_any()))
                .collect(),
        )
    }

    fn span(&self) -> Span;

    fn convert<'a, C: ConvertValue, F: FnMut(TypePathElem<&str>, Val, &Symbols) -> Result<Value>>(
        &self,
        meta: ConvertMeta<'a, F>,
        expected_type: TypeId,
        extra_attributes: Option<&'a Attributes<C>>,
    ) -> Result<Val>;
}

impl ConvertValueInner for Val {
    type Ref = TypePath;

    type Variant = Spanned<TypePathElem>;

    fn get_variant(ident: &Self::Variant, _symbols: &Symbols) -> Result<TypePathElem> {
        Ok(ident.value.clone())
    }

    fn get_asset(asset: &Self::Ref, _symbols: &Symbols) -> Result<TypePath> {
        Ok(asset.clone())
    }

    fn ref_ident(path: &Self::Ref) -> Option<TypePathElem<&str>> {
        TypePathElem::try_from(path.borrow()).ok()
    }

    fn variant_span(variant: &Self::Variant) -> Span {
        variant.span
    }
}

impl ConvertValue for Val {
    fn to_any(&self) -> AnyVal {
        AnyVal::Complete(self)
    }

    fn span(&self) -> Span {
        self.span()
    }

    fn convert<C: ConvertValue, F: FnMut(TypePathElem<&str>, Val, &Symbols) -> Result<Value>>(
        &self,
        meta: ConvertMeta<'_, F>,
        expected_type: TypeId,
        extra_attributes: Option<&Attributes<C>>,
    ) -> Result<Val> {
        let types = meta.symbols.ctx.type_registry();
        let (is_same, can_infer, instanciable) = (
            expected_type == self.ty.value,
            types.can_infer_from(expected_type, self.ty.value),
            types.key_type(expected_type).kind.instanciable(),
        );
        match (is_same, can_infer, instanciable) {
            // If the type is the same or can infer and expected type isn't instantiable.
            (true, true, _) | (false, true, false) => {
                let mut val = self.clone();
                if let Some(extra) = extra_attributes {
                    val = set_attributes(val, extra, meta)?;
                }
                Ok(val)
            }
            // Expected type is instantiable
            (false, true, true) => match &types.key_type(expected_type).kind {
                types::TypeKind::Ref(_)
                | types::TypeKind::Transparent(_)
                | types::TypeKind::Enum { .. } => Self::convert_inner(
                    &self.value,
                    &self.attributes,
                    Some(self.ty),
                    meta,
                    expected_type,
                    extra_attributes,
                ),

                types::TypeKind::Trait(_) | types::TypeKind::Generic(_) => {
                    unreachable!("Expected type is instantiable")
                }

                types::TypeKind::Primitive(_)
                | types::TypeKind::Tuple(_)
                | types::TypeKind::Array(_)
                | types::TypeKind::Map(_)
                | types::TypeKind::Struct(_)
                | types::TypeKind::EnumVariant { .. }
                | types::TypeKind::Or(_) => {
                    unreachable!(
                        "None of these are inferable from something contained in a resolved copy value, {} as {}",
                        types.key_type(self.ty.value).meta.path,
                        types.key_type(expected_type).meta.path,
                    )
                }
            },
            // Can't infer to this type.
            (false, false, _) => {
                // Got wrong type in copy.
                Err(ConversionError::ExpectedExactType {
                    expected: expected_type,
                    got: Some(self.ty.value),
                }
                .spanned(self.value.span))
            }

            // If the type is the same it's always inferable.
            (true, false, _) => unreachable!(),
        }
    }
}

impl ConvertValueInner for CopyVal {
    type Ref = TypePath;

    type Variant = Spanned<TypePathElem>;

    fn get_variant(ident: &Self::Variant, _symbols: &Symbols) -> Result<TypePathElem> {
        Ok(ident.value.clone())
    }

    fn get_asset(asset: &Self::Ref, _symbols: &Symbols) -> Result<TypePath> {
        Ok(asset.clone())
    }

    fn ref_ident(path: &Self::Ref) -> Option<TypePathElem<&str>> {
        TypePathElem::try_from(path.borrow()).ok()
    }

    fn variant_span(variant: &Self::Variant) -> Span {
        variant.span
    }
}

impl ConvertValue for CopyVal {
    fn to_any(&self) -> AnyVal {
        AnyVal::Copy(self)
    }

    fn span(&self) -> Span {
        self.span()
    }

    fn convert<
        'a,
        C: ConvertValue,
        F: FnMut(TypePathElem<&str>, Val, &Symbols) -> Result<Value>,
    >(
        &self,
        meta: ConvertMeta<F>,
        expected_type: TypeId,
        extra_attributes: Option<&Attributes<C>>,
    ) -> Result<Val> {
        match self {
            CopyVal::Copy {
                ty,
                value,
                attributes,
            } => Self::convert_inner(
                value,
                attributes,
                *ty,
                meta,
                expected_type,
                extra_attributes,
            ),
            CopyVal::Resolved(val) => val.convert(meta, expected_type, extra_attributes),
        }
    }
}

impl ConvertValueInner for ParseVal {
    type Ref = Path;

    type Variant = Path;

    fn get_variant(ident: &Self::Variant, symbols: &Symbols) -> Result<TypePathElem> {
        Ok(symbols
            .ctx
            .type_registry()
            .key_type(symbols.resolve_type(ident)?)
            .meta
            .path
            .get_end()
            .expect("We can't have empty paths for referable assets")
            .1
            .to_owned())
    }

    fn get_asset(asset: &Self::Ref, symbols: &Symbols) -> Result<TypePath> {
        symbols.resolve_asset(asset).map(|(_, p)| p)
    }

    fn ref_ident(path: &Self::Ref) -> Option<TypePathElem<&str>> {
        path.as_ident()
            .and_then(|p| TypePathElem::new(p.value).ok())
    }

    fn variant_span(variant: &Self::Variant) -> Span {
        variant.span()
    }
}

impl ConvertValue for ParseVal {
    fn to_any(&self) -> AnyVal {
        AnyVal::Parse(self)
    }

    fn span(&self) -> Span {
        Span::new(
            self.value.span,
            self.attributes.span.start..self.value.span.end,
        )
    }

    fn convert<
        'a,
        C: ConvertValue,
        F: FnMut(TypePathElem<&str>, Val, &Symbols) -> Result<Value>,
    >(
        &self,
        meta: ConvertMeta<F>,
        expected_type: TypeId,
        extra_attributes: Option<&Attributes<C>>,
    ) -> Result<Val> {
        let ty = value_type(self, meta.symbols)?;

        Self::convert_inner(
            &self.value,
            &self.attributes,
            ty,
            meta,
            expected_type,
            extra_attributes,
        )
    }
}

impl ConvertValue for AnyVal<'_> {
    fn to_any(&self) -> AnyVal {
        *self
    }

    fn to_any_attributes(attributes: &Attributes<Self>) -> Attributes<AnyVal<'_>> {
        attributes.clone()
    }

    fn span(&self) -> Span {
        match self {
            AnyVal::Parse(v) => v.span(),
            AnyVal::Copy(v) => v.span(),
            AnyVal::Complete(v) => v.span(),
        }
    }

    fn convert<C: ConvertValue, F: FnMut(TypePathElem<&str>, Val, &Symbols) -> Result<Value>>(
        &self,
        meta: ConvertMeta<F>,
        expected_type: TypeId,
        extra_attributes: Option<&Attributes<C>>,
    ) -> Result<Val> {
        match self {
            AnyVal::Parse(v) => v.convert(meta, expected_type, extra_attributes),
            AnyVal::Copy(v) => v.convert(meta, expected_type, extra_attributes),
            AnyVal::Complete(v) => v.convert(meta, expected_type, extra_attributes),
        }
    }
}

pub(super) fn convert_copy_value<F: FnMut(TypePathElem<&str>, Val, &Symbols) -> Result<Value>>(
    value: &ParseVal,
    mut meta: ConvertMeta<F>,
) -> Result<CopyVal> {
    let types = meta.symbols.ctx.type_registry();
    let val_type = value_type(value, meta.symbols)?;

    if let Some(val_type) = val_type.as_ref()
        && types.key_type(val_type.value).kind.instanciable()
    {
        let val_type =
            default_value_type(meta.symbols, value.value.primitive_type(), Some(*val_type))
                .unwrap_or(val_type.value);
        value
            .convert(meta, val_type, no_attr())
            .map(CopyVal::Resolved)
    } else {
        let mut parse_attributes = || {
            value
                .attributes
                .0
                .iter()
                .map(|(ident, value)| {
                    Ok::<_, Spanned<ConversionError>>((
                        ident.clone(),
                        convert_copy_value(value, meta.reborrow())?,
                    ))
                })
                .try_collect::<indexmap::IndexMap<_, _>>()
        };

        let attributes = parse_attributes()?;
        let inner: Value<CopyVal> = match &value.value.value {
            Value::Primitive(p) => Value::Primitive(p.clone()),
            Value::Ref(_) => todo!(),
            Value::Tuple(seq) => Value::Tuple(
                seq.iter()
                    .map(|v| convert_copy_value(v, meta.reborrow()))
                    .collect::<Result<_>>()?,
            ),
            Value::Array(seq) => Value::Array(
                seq.iter()
                    .map(|v| convert_copy_value(v, meta.reborrow()))
                    .collect::<Result<_>>()?,
            ),
            Value::Map(map) => Value::Map(
                map.iter()
                    .map(|(key, value)| {
                        Ok((
                            convert_copy_value(key, meta.reborrow())?,
                            convert_copy_value(value, meta.reborrow())?,
                        ))
                    })
                    .collect::<Result<_>>()?,
            ),
            Value::Struct(fields_kind) => Value::Struct(match fields_kind {
                FieldsKind::Unit => FieldsKind::Unit,
                FieldsKind::Unnamed(seq) => FieldsKind::Unnamed(
                    seq.iter()
                        .map(|v| convert_copy_value(v, meta.reborrow()))
                        .collect::<Result<_>>()?,
                ),
                FieldsKind::Named(fields) => FieldsKind::Named(
                    fields
                        .iter()
                        .map(|(field, v)| {
                            Ok((field.clone(), convert_copy_value(v, meta.reborrow())?))
                        })
                        .collect::<Result<_>>()?,
                ),
            }),
            Value::Or(paths) => Value::Or(
                paths
                    .iter()
                    .map(|path| {
                        let ident = path.last_ident();
                        Ok(TypePathElem::new(ident.value)
                            .map_err(|e| e.spanned(ident.span))?
                            .to_owned()
                            .spanned(ident.span))
                    })
                    .collect::<Result<_>>()?,
            ),
            Value::Transparent(inner) => {
                Value::Transparent(Box::new(convert_copy_value(inner, meta)?))
            }
            Value::Enum(_, _) => unimplemented!("We don't get enums from parsing"),
        };

        Ok(CopyVal::Copy {
            ty: val_type,
            value: inner.spanned(value.value.span),
            attributes: Attributes(attributes).spanned(value.attributes.span),
        })
    }
}
