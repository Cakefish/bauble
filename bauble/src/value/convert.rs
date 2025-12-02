use std::collections::HashMap;

use crate::{
    ConversionError, FieldsKind, PrimitiveValue, Span,
    parse::ParseVal,
    path::{TypePath, TypePathElem},
    spanned::{SpanExt, Spanned},
    types::{self, TypeId},
    value::{
        Attributes, Fields, Ident, SpannedValue, Symbols, UnspannedVal, Val, Value, ValueContainer,
        ValueTrait, error::Result,
    },
};

pub fn no_attr() -> Option<&'static Attributes<Val>> {
    None
}

fn set_attributes<C: ConvertValue>(
    mut val: Val,
    attributes: &Attributes<C>,
    mut meta: ConvertMeta,
) -> Result<Val> {
    let types = meta.symbols.ctx.type_registry();
    let ty = types.key_type(val.ty.value);

    for (ident, value) in attributes.iter() {
        let ident = C::get_spanned_field(ident, &meta);
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

        val.attributes.insert(ident, value);
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

    let ty = match &*value.value {
        Value::Ref(path) => Some(symbols.resolve_asset(path)?.0.spanned(path.span())),
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
pub enum AnyVal<'a> {
    Parse(&'a ParseVal),
    Complete(&'a Val),
    Unspanned(&'a UnspannedVal),
}

pub struct ConvertMeta<'a> {
    pub symbols: &'a Symbols<'a>,
    pub additional_objects: &'a mut AdditionalObjects,
    // TODO: in stage 2 (of asset per file impl) this probably needs to be `0` rather than anything
    // that could conflict with the name of a local asset. Because this is used to name inline
    // objects uniquely.
    //
    /// Used as a prefix to uniquely name inline objects.
    pub object_name: TypePathElem<&'a str>,
    pub default_span: Span,
}

impl ConvertMeta<'_> {
    pub fn reborrow(&mut self) -> ConvertMeta {
        ConvertMeta {
            symbols: self.symbols,
            additional_objects: self.additional_objects,
            object_name: self.object_name,
            default_span: self.default_span,
        }
    }

    fn with_object_name<'b>(&'b mut self, name: TypePathElem<&'b str>) -> ConvertMeta<'b> {
        ConvertMeta {
            symbols: self.symbols,
            additional_objects: self.additional_objects,
            object_name: name,
            default_span: self.default_span,
        }
    }
}

/// Represents additional objects added when parsing other objects.
///
/// Also known as sub-assets.
pub(super) struct AdditionalObjects {
    objects: Vec<super::Object>,
    name_allocs: std::collections::HashMap<TypePathElem, u64>,
    file_path: TypePath,
}

impl AdditionalObjects {
    /// Create a new instance for a given file.
    pub(super) fn new(file_path: TypePath) -> Self {
        Self {
            file_path,
            name_allocs: Default::default(),
            objects: Default::default(),
        }
    }

    /// Adds an additional object, and returns a reference value to that object.
    fn add_object(
        &mut self,
        name: TypePathElem<&str>,
        val: Val,
        symbols: &Symbols,
    ) -> Result<Value> {
        let idx = *self
            .name_allocs
            .entry(name.to_owned())
            .and_modify(|i| *i += 1u64)
            .or_insert(0);
        let name = TypePathElem::new(format!("{name}@{idx}"))
            .expect("idx is just a number, and we know name is a valid path elem.");

        self.objects.push(super::create_object(
            self.file_path.join(&name),
            false,
            val,
            symbols,
        )?);

        Ok(Value::Ref(self.file_path.join(&name)))
    }

    pub(super) fn into_objects(self) -> Vec<super::Object> {
        self.objects
    }

    pub fn with_additional_unspanned<R>(
        &mut self,
        span: Span,
        object_name: TypePathElem<&str>,
        symbols: &Symbols,
        f: impl FnOnce(&mut AdditionalUnspannedObjects) -> R,
    ) -> Result<R> {
        let mut unspanned = AdditionalUnspannedObjects::new_with_name_allocs(
            self.file_path.borrow(),
            object_name,
            &mut self.name_allocs,
        );

        let res = f(&mut unspanned);

        for (name, value) in unspanned.into_objects() {
            self.objects.push(super::create_object(
                self.file_path.join(&name),
                false,
                value.into_spanned(span),
                symbols,
            )?);
        }

        Ok(res)
    }
}

enum NameAllocs<'a> {
    Owned(std::collections::HashMap<TypePathElem, u64>),
    Borrowed(&'a mut std::collections::HashMap<TypePathElem, u64>),
}

impl NameAllocs<'_> {
    fn get_mut(&mut self) -> &mut std::collections::HashMap<TypePathElem, u64> {
        match self {
            NameAllocs::Owned(m) => m,
            NameAllocs::Borrowed(m) => m,
        }
    }
}

/// A helper struct to allocate extra objects in bauble types `default`.
pub struct AdditionalUnspannedObjects<'a> {
    file_path: TypePath<&'a str>,
    object_name: TypePathElem<&'a str>,
    objects: Vec<(TypePathElem, UnspannedVal)>,
    name_allocs: NameAllocs<'a>,
}

impl<'a> AdditionalUnspannedObjects<'a> {
    /// Create a new instance with it's own checking of duplicate names.
    pub fn new(file_path: TypePath<&'a str>, object_name: TypePathElem<&'a str>) -> Self {
        Self {
            file_path,
            object_name,
            objects: Vec::new(),
            name_allocs: NameAllocs::Owned(std::collections::HashMap::default()),
        }
    }

    /// Create a new instance borrowing a map to create unique names.
    pub fn new_with_name_allocs(
        file_path: TypePath<&'a str>,
        object_name: TypePathElem<&'a str>,
        name_allocs: &'a mut HashMap<TypePathElem, u64>,
    ) -> Self {
        Self {
            file_path,
            object_name,
            objects: Vec::new(),
            name_allocs: NameAllocs::Borrowed(name_allocs),
        }
    }

    /// Add the type id to the path this keeps track of, for better unique names for sub-objects.
    pub fn in_type<R>(
        &mut self,
        ty: TypeId,
        f: impl FnOnce(&mut AdditionalUnspannedObjects) -> R,
    ) -> R {
        let name = TypePathElem::new(format!("{}&{}", self.object_name, ty.inner())).unwrap();

        let mut inner = AdditionalUnspannedObjects::new_with_name_allocs(
            self.file_path,
            name.borrow(),
            self.name_allocs.get_mut(),
        );

        let res = f(&mut inner);

        self.objects.extend(inner.into_objects());

        res
    }

    /// Add an additional object, and get a reference to it.
    pub fn add_object(&mut self, val: UnspannedVal) -> Value<UnspannedVal> {
        let idx = *self
            .name_allocs
            .get_mut()
            .entry(self.object_name.to_owned())
            .and_modify(|i| *i += 1u64)
            .or_insert(0);
        let name = TypePathElem::new(format!("{}@{idx}", self.object_name))
            .expect("idx is just a number, and we know name is a valid path elem.");

        let res = Value::Ref(self.file_path.join(&name));

        self.objects.push((name, val));

        res
    }

    /// Get the additional objects.
    pub fn into_objects(
        self,
    ) -> impl ExactSizeIterator<Item = (TypePathElem, UnspannedVal)> + use<> {
        self.objects.into_iter()
    }
}

/// This trait has an implementation to convert any `Value` into a finished `Val`.
trait ConvertValueInner:
    ConvertValue + ValueTrait + ValueContainer<ContainerField = Self::Field>
where
    Self::Inner: ConvertValue<ContainerField = <Self as ValueTrait>::Field>,
{
    fn variant_span(variant: &Self::Variant, meta: &ConvertMeta) -> Span;

    fn get_variant(ident: &Self::Variant, symbols: &Symbols) -> Result<TypePathElem>;

    fn get_asset(ident: &Self::Ref, symbols: &Symbols) -> Result<TypePath>;

    fn convert_inner<'a, C: ConvertValue>(
        value: Spanned<&Value<Self>>,
        attributes: Spanned<&Attributes<Self::Inner>>,
        val_ty: Option<Spanned<TypeId>>,
        mut meta: ConvertMeta<'a>,
        expected_type: TypeId,
        extra_attributes: Option<&'a Attributes<C>>,
    ) -> Result<Val> {
        let raw_val_type = val_ty;
        let mut val_ty = val_ty.or(matches!(
            value.value,
            Value::Primitive(PrimitiveValue::Default)
        )
        .then_some(expected_type.spanned(value.span)));

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
                        ConversionError::WrongLength { got: l, ty: *ty_id }
                            .spanned(value.get_span(&meta))
                    })?;

                    seq.push(value.convert(meta.reborrow(), ty, no_attr())?);
                }

                seq
            }};
        }

        /// A struct to store extra attributes, this is mostly to avoid allocations in most cases.
        enum ExtraAttributes<'a, C0: ConvertValue, C1: ConvertValue> {
            None,
            BorrowedA(&'a Attributes<C0>),
            BorrowedB(&'a Attributes<C1>),
            BorrowedC(&'a Attributes<Val>),
            Owned(Attributes<AnyVal<'a>>),
        }

        impl<'a, C0: ConvertValue, C1: ConvertValue> ExtraAttributes<'a, C0, C1> {
            fn get_mut(&mut self, meta: &ConvertMeta) -> &mut Attributes<AnyVal<'a>> {
                match self {
                    ExtraAttributes::None => {
                        *self = ExtraAttributes::Owned(Attributes::default());

                        self.get_mut(meta)
                    }
                    ExtraAttributes::BorrowedA(attributes) => {
                        *self = ExtraAttributes::Owned(C0::to_any_attributes(attributes, meta));

                        self.get_mut(meta)
                    }
                    ExtraAttributes::BorrowedB(attributes) => {
                        *self = ExtraAttributes::Owned(C1::to_any_attributes(attributes, meta));

                        self.get_mut(meta)
                    }
                    ExtraAttributes::BorrowedC(attributes) => {
                        *self = ExtraAttributes::Owned(Val::to_any_attributes(attributes, meta));

                        self.get_mut(meta)
                    }
                    ExtraAttributes::Owned(attributes) => attributes,
                }
            }

            pub fn extend(&mut self, attributes: &'a Attributes<Val>, meta: &ConvertMeta) {
                if self.is_empty() {
                    *self = ExtraAttributes::BorrowedC(attributes);
                } else {
                    self.get_mut(meta).0.extend(
                        attributes
                            .iter()
                            .map(|(ident, v)| (ident.clone(), v.to_any())),
                    );
                }
            }

            fn convert_with(
                &mut self,
                value: &C1,
                meta: ConvertMeta,
                expected_type: TypeId,
            ) -> Result<Val>
            where
                C1: ConvertValue,
            {
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

            fn convert_inner_with<
                Outer: ConvertValueInner<Inner = C1, Field = C1::ContainerField>,
            >(
                &mut self,
                value: Spanned<&Value<Outer>>,
                attributes: Spanned<&Attributes<C1>>,
                val_ty: Option<Spanned<TypeId>>,
                meta: ConvertMeta,
                expected_type: TypeId,
            ) -> Result<Val>
            where
                C1: ConvertValue,
            {
                match std::mem::replace(self, ExtraAttributes::None) {
                    ExtraAttributes::None => Outer::convert_inner(
                        value,
                        attributes,
                        val_ty,
                        meta,
                        expected_type,
                        no_attr(),
                    ),
                    ExtraAttributes::BorrowedA(extra_attributes) => Outer::convert_inner(
                        value,
                        attributes,
                        val_ty,
                        meta,
                        expected_type,
                        Some(extra_attributes),
                    ),
                    ExtraAttributes::BorrowedB(extra_attributes) => Outer::convert_inner(
                        value,
                        attributes,
                        val_ty,
                        meta,
                        expected_type,
                        Some(extra_attributes),
                    ),
                    ExtraAttributes::BorrowedC(extra_attributes) => Outer::convert_inner(
                        value,
                        attributes,
                        val_ty,
                        meta,
                        expected_type,
                        Some(extra_attributes),
                    ),
                    ExtraAttributes::Owned(extra_attributes) => Outer::convert_inner(
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

            fn first(&self, meta: &ConvertMeta) -> Option<Ident> {
                match self {
                    ExtraAttributes::None => None,
                    ExtraAttributes::BorrowedA(attributes) => attributes
                        .first()
                        .map(|(k, _)| C0::get_spanned_field(k, meta)),
                    ExtraAttributes::BorrowedB(attributes) => attributes
                        .first()
                        .map(|(k, _)| C1::get_spanned_field(k, meta)),
                    ExtraAttributes::BorrowedC(attributes) => {
                        attributes.first().map(|(k, _)| k.clone())
                    }
                    ExtraAttributes::Owned(attributes) => {
                        attributes.first().map(|(k, _)| k.clone())
                    }
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
            let mut extra_attributes: ExtraAttributes<C, Self::Inner> =
                if let Some(extra_attributes) = extra_attributes {
                    for (ident, v) in extra_attributes {
                        let ident = C::get_spanned_field(ident, &meta);
                        let Some(ty) = ty.meta.attributes.get(ident.as_str()) else {
                            continue;
                        };

                        new_attrs.insert(ident, v.convert(meta.reborrow(), ty.id, no_attr())?);
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
                                .filter(|(i, _)| {
                                    new_attrs
                                        .get(C::get_spanned_field(i, &meta).as_str())
                                        .is_none()
                                })
                                .map(|(i, v)| {
                                    (C::get_spanned_field(i, &meta), v.container_to_any())
                                })
                                .collect(),
                        ))
                    }
                } else {
                    ExtraAttributes::None
                };

            let old_len = new_attrs.len();
            let empty = extra_attributes.is_empty();
            // And then we take from our own attributes, putting duplicates and extra stuff in `extra_attributes`.
            for (ident, v) in attributes.value {
                let ident = Self::get_spanned_field(ident, &meta);
                let (Some(ty), false) = (
                    ty.meta.attributes.get(ident.as_str()),
                    new_attrs.get(ident.as_str()).is_some(),
                ) else {
                    if !empty {
                        let extra = extra_attributes.get_mut(&meta);
                        if let Some((first, _)) = extra.get(ident.as_str()) {
                            Err(ConversionError::DuplicateAttribute {
                                first: first.clone(),
                                second: ident.clone(),
                            }
                            .spanned(ident.span))?
                        }

                        extra.insert(ident.clone(), v.container_to_any());
                    }
                    continue;
                };
                // We checked that `new_attributes` didn't contain this field.
                new_attrs.insert(ident.clone(), v.convert(meta.reborrow(), ty.id, no_attr())?);
            }

            if empty {
                extra_attributes = if new_attrs.len() == old_len {
                    // All of the extra attributes left.
                    ExtraAttributes::BorrowedB(attributes.value)
                } else if new_attrs.len() == old_len + attributes.len() {
                    // None of the extra attributes left.
                    ExtraAttributes::None
                } else {
                    // Part of the extra attributes left.
                    ExtraAttributes::Owned(Attributes(
                        attributes
                            .iter()
                            .filter(|(i, _)| {
                                new_attrs
                                    .get(Self::get_spanned_field(i, &meta).as_str())
                                    .is_none()
                            })
                            .map(|(i, v)| (Self::get_spanned_field(i, &meta), v.container_to_any()))
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

        let val = 'val: {
            let value = match (&ty.kind, &value.value) {
                (_, Value::Primitive(PrimitiveValue::Default))
                    if val_ty.is_none_or(|t| t == ty_id) && ty.meta.default.is_some() =>
                {
                    let mut v = meta.additional_objects.with_additional_unspanned(
                        span,
                        meta.object_name,
                        meta.symbols,
                        |additional| {
                            ty.meta
                                .default
                                .map(|v| v(additional, types, *ty_id).into_spanned(span))
                                .expect("We checked that this is some in the match")
                        },
                    )?;

                    for (s, value) in attributes.into_iter() {
                        v.attributes.insert(s, value);
                    }

                    break 'val v;
                }
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
                            let field = Self::get_spanned_field(field, &meta);
                            let Some(ty) = fields.get(field.as_str()) else {
                                Err(ConversionError::UnexpectedField {
                                    attribute: false,
                                    field: field.clone(),
                                    ty: *ty_id,
                                }
                                .spanned(span))?
                            };

                            new_fields
                                .insert(field, value.convert(meta.reborrow(), ty.id, no_attr())?);
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
                            .spanned(Self::variant_span(variant, &meta));
                        let ty = variants.get(&*variant).ok_or_else(|| {
                            ConversionError::UnknownVariant {
                                variant: variant.clone(),
                                ty: ty_id.value,
                            }
                            .spanned(span)
                        })?;
                        (
                            variant.map(|v| v.to_owned()),
                            extra_attributes.convert_with(value, meta.reborrow(), ty)?,
                        )
                    }
                    // Otherwise see if we have the value of an `EnumVariant` or its generic type.
                    else if let Some(raw_val_type) = raw_val_type
                        && let Some((variant, variant_ty)) = variants.iter().find(|(_, ty)| {
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
                                Spanned::new(attributes_span, &Default::default()),
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
                                            Spanned::new(attributes_span, &Default::default()),
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
                                .spanned(Self::variant_span(ident, &meta)))
                        })
                        .collect::<Result<_>>()?;

                    Value::Or(variants)
                }
                // A ref can convert from a ref value.
                (types::TypeKind::Ref(_), Value::Ref(r)) => {
                    Value::Ref(Self::get_asset(r, meta.symbols)?)
                }
                // Or from another value, and we instantiate a new object that we can refer to.
                (types::TypeKind::Ref(ty), _) => {
                    let object_name =
                        TypePathElem::new(format!("{}&{}", meta.object_name, ty.inner()))
                            .expect("We didn't add any ::");
                    let val = extra_attributes.convert_inner_with(
                        value,
                        Spanned::new(attributes_span, &Default::default()),
                        raw_val_type,
                        meta.with_object_name(object_name.borrow()),
                        *ty,
                    )?;

                    meta.additional_objects
                        .add_object(object_name.borrow(), val, meta.symbols)?
                }
                (types::TypeKind::Primitive(primitive), Value::Primitive(value))
                    if !matches!(value, PrimitiveValue::Default) =>
                {
                    Value::Primitive(match (primitive, value) {
                        (types::Primitive::Num, PrimitiveValue::Num(v)) => PrimitiveValue::Num(*v),
                        (types::Primitive::Bool, PrimitiveValue::Bool(v)) => {
                            PrimitiveValue::Bool(*v)
                        }
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
                    // If the value type is this transparent type, project it to the represented value.
                    let val_ty = if raw_val_type.is_some_and(|v| *v == *ty_id) {
                        raw_val_type.map(|v| v.map(|_| *ty))
                    } else {
                        raw_val_type
                    };
                    let val = extra_attributes.convert_inner_with(
                        value,
                        Spanned::new(attributes_span, &Default::default()),
                        val_ty,
                        meta.reborrow(),
                        *ty,
                    )?;

                    Value::Transparent(Box::new(val))
                }
                (_, Value::Transparent(value)) => {
                    // Try again as if it wasn't a transparent value.
                    extra_attributes.extend(&attributes, &meta);
                    break 'val extra_attributes.convert_with(
                        value,
                        meta.reborrow(),
                        expected_type,
                    )?;
                }
                (_, Value::Primitive(PrimitiveValue::Default)) => {
                    let mut v = meta.additional_objects.with_additional_unspanned(
                        span,
                        meta.object_name,
                        meta.symbols,
                        |additional| -> Result<_> {
                            Ok(types
                                .instantiate(*ty_id, additional)
                                .ok_or(ty_id.map(|ty| ConversionError::NotInstantiable { ty }))?
                                .into_spanned(value.span))
                        },
                    )??;

                    for (s, value) in attributes.into_iter() {
                        v.attributes.insert(s, value);
                    }

                    break 'val v;
                }
                _ => Err(expected_err())?,
            };

            // Report errors for unexpected attributes
            if let Some(ident) = extra_attributes.first(&meta) {
                Err(ConversionError::UnexpectedField {
                    attribute: true,
                    field: ident.clone(),
                    ty: *ty_id,
                }
                .spanned(attributes_span))?;
            }

            Val {
                ty: ty_id,
                value: value.spanned(span),
                attributes: attributes.spanned(attributes_span),
            }
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
/// There are two stages of bauble values:
/// 1. `ParseVal`, which we get when we parse bauble from types.
/// 2. `Val`, the fully resolved type, which is always correct to convert to rust.
pub(super) trait ConvertValue: ValueContainer {
    fn get_spanned_field(field: &Self::ContainerField, meta: &ConvertMeta) -> Ident;

    fn to_any_attributes<'a>(
        attributes: &'a Attributes<Self>,
        meta: &ConvertMeta,
    ) -> Attributes<AnyVal<'a>> {
        Attributes(
            attributes
                .0
                .iter()
                .map(|(i, v)| (Self::get_spanned_field(i, meta), v.container_to_any()))
                .collect(),
        )
    }

    fn get_span(&self, meta: &ConvertMeta) -> Span {
        meta.default_span
    }

    fn convert<'a, C: ConvertValue>(
        &self,
        meta: ConvertMeta<'a>,
        expected_type: TypeId,
        extra_attributes: Option<&'a Attributes<C>>,
    ) -> Result<Val>;
}

impl ConvertValueInner for UnspannedVal {
    fn get_variant(ident: &Self::Variant, _symbols: &Symbols) -> Result<TypePathElem> {
        Ok(ident.clone())
    }

    fn get_asset(asset: &Self::Ref, _symbols: &Symbols) -> Result<TypePath> {
        Ok(asset.clone())
    }

    fn variant_span(_variant: &Self::Variant, meta: &ConvertMeta) -> Span {
        meta.default_span
    }
}

impl ConvertValue for UnspannedVal {
    fn get_spanned_field(field: &Self::ContainerField, meta: &ConvertMeta) -> Ident {
        field.clone().spanned(meta.default_span)
    }

    fn convert<'a, C: ConvertValue>(
        &self,
        meta: ConvertMeta<'a>,
        expected_type: TypeId,
        extra_attributes: Option<&'a Attributes<C>>,
    ) -> Result<Val> {
        let val_ty = Some(self.ty.spanned(meta.default_span));
        Self::convert_inner(
            (&self.value).spanned(meta.default_span),
            (&self.attributes).spanned(meta.default_span),
            val_ty,
            meta,
            expected_type,
            extra_attributes,
        )
    }
}

impl ConvertValueInner for Val {
    fn get_variant(ident: &Self::Variant, _symbols: &Symbols) -> Result<TypePathElem> {
        Ok(ident.value.clone())
    }

    fn get_asset(asset: &Self::Ref, _symbols: &Symbols) -> Result<TypePath> {
        Ok(asset.clone())
    }

    fn variant_span(variant: &Self::Variant, _meta: &ConvertMeta) -> Span {
        variant.span
    }
}

impl ConvertValue for Val {
    fn get_spanned_field(field: &Self::ContainerField, _meta: &ConvertMeta) -> Ident {
        field.clone()
    }

    fn get_span(&self, _meta: &ConvertMeta) -> Span {
        self.span()
    }

    fn convert<C: ConvertValue>(
        &self,
        meta: ConvertMeta<'_>,
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
                    self.value.as_ref(),
                    self.attributes.as_ref(),
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

impl ConvertValueInner for ParseVal {
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

    fn variant_span(variant: &Self::Variant, _meta: &ConvertMeta) -> Span {
        variant.span()
    }
}

impl ConvertValue for ParseVal {
    fn get_spanned_field(field: &Self::ContainerField, _meta: &ConvertMeta) -> Ident {
        field.clone()
    }

    fn get_span(&self, _meta: &ConvertMeta) -> Span {
        self.span()
    }

    fn convert<'a, C: ConvertValue>(
        &self,
        meta: ConvertMeta,
        expected_type: TypeId,
        extra_attributes: Option<&Attributes<C>>,
    ) -> Result<Val> {
        let ty = value_type(self, meta.symbols)?;

        Self::convert_inner(
            self.value.as_ref(),
            self.attributes.as_ref(),
            ty,
            meta,
            expected_type,
            extra_attributes,
        )
    }
}

impl ConvertValue for AnyVal<'_> {
    fn get_spanned_field(field: &Self::ContainerField, _meta: &ConvertMeta) -> Ident {
        field.clone()
    }

    fn get_span(&self, meta: &ConvertMeta) -> Span {
        match self {
            AnyVal::Parse(v) => v.get_span(meta),
            AnyVal::Complete(v) => v.get_span(meta),
            AnyVal::Unspanned(v) => v.get_span(meta),
        }
    }

    fn convert<C: ConvertValue>(
        &self,
        meta: ConvertMeta,
        expected_type: TypeId,
        extra_attributes: Option<&Attributes<C>>,
    ) -> Result<Val> {
        match self {
            AnyVal::Parse(v) => v.convert(meta, expected_type, extra_attributes),
            AnyVal::Complete(v) => v.convert(meta, expected_type, extra_attributes),
            AnyVal::Unspanned(v) => v.convert(meta, expected_type, extra_attributes),
        }
    }
}
