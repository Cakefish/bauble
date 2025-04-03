use std::{
    collections::{HashMap, HashSet},
    ptr::{DynMetadata, Pointee},
};

pub mod path;

use indexmap::IndexMap;
use path::{TypePath, TypePathElem};

use crate::{Bauble, BaubleAllocator, value::UnspannedVal};

pub trait BaubleTrait: Pointee<Metadata = DynMetadata<Self>> + 'static {
    const BAUBLE_PATH: &'static str;
}

impl BaubleTrait for dyn std::any::Any {
    const BAUBLE_PATH: &'static str = "std::Any";
}

impl BaubleTrait for dyn std::fmt::Debug {
    const BAUBLE_PATH: &'static str = "std::Debug";
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TypeId(usize);

impl TypeId {
    pub fn inner(&self) -> usize {
        self.0
    }
}

impl From<TraitId> for TypeId {
    fn from(value: TraitId) -> Self {
        value.0
    }
}

impl From<GenericTypeId> for TypeId {
    fn from(value: GenericTypeId) -> Self {
        value.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct GenericTypeId(TypeId);

/// We maintain the invariant that the type is kind `TypeKind::Trait`
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TraitId(TypeId);

#[derive(Clone, Debug)]
enum SealedTypeSet {
    All,
    Certain(HashSet<TypeId>),
}

#[derive(Debug, Clone)]
pub struct TypeSet(SealedTypeSet);

impl TypeSet {
    pub fn insert(&mut self, ty: TypeId) -> bool {
        match &mut self.0 {
            SealedTypeSet::All => false,
            SealedTypeSet::Certain(set) => set.insert(ty),
        }
    }

    pub fn contains(&self, ty: TypeId) -> bool {
        match &self.0 {
            SealedTypeSet::All => true,
            SealedTypeSet::Certain(set) => set.contains(&ty),
        }
    }
}

pub struct Trait {
    pub path: TypePath,
    /// A type that can represent this trait.
    pub ty: TypeId,
    /// Types we know that implement this trait.
    pub types: TypeSet,
}

#[derive(Clone, Debug)]
pub struct TypeRegistry {
    types: Vec<Type>,

    asset_refs: HashMap<TypeId, TypeId>,

    generic: HashMap<TypePath, TypeId>,
    type_from_rust: HashMap<std::any::TypeId, TypeId>,
    to_be_assigned: HashSet<TypeId>,

    top_level_trait_dependency: TraitId,

    primitive_types: [TypeId; 5],
}

pub enum VariantKind {
    Flattened(TypeKind),
    Explicit(Fields),
}

pub struct Variant {
    pub ident: TypePathElem,
    pub kind: VariantKind,
    pub attributes: NamedFields,
    pub extra_validation: Option<ValidationFunction>,
    pub extra: IndexMap<String, String>,
    pub default: Option<UnspannedVal>,
}

impl Variant {
    pub fn explicit(ident: TypePathElem<impl AsRef<str>>, fields: Fields) -> Self {
        Self {
            ident: ident.to_owned(),
            kind: VariantKind::Explicit(fields),
            attributes: Default::default(),
            extra_validation: None,
            extra: Default::default(),
            default: None,
        }
    }

    pub fn flattened(ident: TypePathElem<impl AsRef<str>>, ty: TypeKind) -> Self {
        Self {
            ident: ident.to_owned(),
            kind: VariantKind::Flattened(ty),
            attributes: Default::default(),
            extra_validation: None,
            extra: Default::default(),
            default: None,
        }
    }

    pub fn with_attributes(mut self, attributes: NamedFields) -> Self {
        self.attributes = attributes;
        self
    }

    pub fn with_extra(mut self, extra: IndexMap<String, String>) -> Self {
        self.extra = extra;
        self
    }

    pub fn with_validation(mut self, validation: ValidationFunction) -> Self {
        self.extra_validation = Some(validation);
        self
    }

    pub fn with_default(mut self, value: UnspannedVal) -> Self {
        self.default = Some(value);
        self
    }
}

#[derive(Debug)]
pub enum TypeSystemError<'a> {
    ToBeAssigned(Vec<(TypeId, TypePath<&'a str>)>),
    NotInstantiable {
        ty_id: TypeId,
        ty: TypePath<&'a str>,
    },
    InstantiableErrors,
    ConstructInequality(UnspannedVal, UnspannedVal),
}

impl TypeRegistry {
    pub(crate) fn new() -> Self {
        let mut this = Self {
            types: Default::default(),

            asset_refs: Default::default(),

            // NOTE: Top level values always have to derive from this trait.
            top_level_trait_dependency: Self::any_trait(),

            to_be_assigned: Default::default(),

            generic: Default::default(),
            type_from_rust: Default::default(),

            primitive_types: [Self::any_type(); 5],
        };

        // The element at index 0 is always any trait
        let any_trait = this.get_or_register_trait::<dyn std::any::Any>();
        this.types[any_trait.0.0].kind = TypeKind::Trait(TypeSet(SealedTypeSet::All));

        // The element at index 1 is any trait.
        let any_id = this.get_or_register_type::<crate::Val, crate::DefaultAllocator>();

        this.set_primitive_default_type(any_id);

        let float_id = this.get_or_register_type::<f32, crate::DefaultAllocator>();
        this.set_primitive_default_type(float_id);

        let string_id = this.get_or_register_type::<String, crate::DefaultAllocator>();
        this.set_primitive_default_type(string_id);

        let bool_id = this.get_or_register_type::<bool, crate::DefaultAllocator>();
        this.set_primitive_default_type(bool_id);

        let unit_id = this.get_or_register_type::<(), crate::DefaultAllocator>();
        this.set_primitive_default_type(unit_id);

        this
    }

    /// If a type implements the required top-level type.
    pub fn impls_top_level_type(&self, id: TypeId) -> bool {
        self.key_trait(self.top_level_trait_dependency).contains(id)
    }

    pub fn top_level_trait(&self) -> TraitId {
        self.top_level_trait_dependency
    }

    /// This is present in all `TypeRegistry`
    pub fn any_trait() -> TraitId {
        TraitId(TypeId(0))
    }

    /// This is present in all `TypeRegistry`
    pub fn any_type() -> TypeId {
        TypeId(1)
    }

    /// Sets what type this primitive type should use by default.
    ///
    /// For example, if you register a type with `TypeKind::Primitive(Primitive::Str)`
    /// that type will then be used whenever we have a string bauble value we can't
    /// resolve the type for.
    ///
    /// # Panics
    ///
    /// Panics if the `TypeKind` of this type isn't a primitive.
    pub fn set_primitive_default_type(&mut self, id: TypeId) {
        let TypeKind::Primitive(primitive) = self.key_type(id).kind else {
            panic!("Tried to set a non-primitive type as a primitive default type")
        };

        self.primitive_types[primitive as usize] = id;
    }

    pub fn primitive_type(&self, primitive: Primitive) -> TypeId {
        self.primitive_types[primitive as usize]
    }

    pub fn type_id_of_std_id(&self, id: std::any::TypeId) -> Option<TypeId> {
        self.type_from_rust.get(&id).copied()
    }

    pub fn type_id<'a, T: Bauble<'a, A>, A: BaubleAllocator<'a>>(&self) -> Option<TypeId> {
        self.type_id_of_std_id(std::any::TypeId::of::<T>())
    }

    pub fn trait_id<T: ?Sized + BaubleTrait>(&self) -> Option<TraitId> {
        self.type_id_of_std_id(std::any::TypeId::of::<T>())
            .map(TraitId)
    }

    pub fn type_ids(&self) -> impl Iterator<Item = TypeId> {
        (0..self.types.len()).map(TypeId)
    }

    fn register_type(&mut self, f: impl FnOnce(&mut Self, TypeId) -> Type) -> TypeId {
        let id = TypeId(self.types.len());

        // Push a temporary to reserve id.
        self.types.push(Type {
            meta: TypeMeta::default(),
            kind: TypeKind::Primitive(Primitive::Any),
        });
        let ty = f(self, id);
        self.types[id.0] = ty;

        id
    }

    #[must_use]
    /// Build `EnumVariants`.
    pub fn build_enum(&mut self, variants: impl IntoIterator<Item = Variant>) -> EnumVariants {
        EnumVariants(
            variants
                .into_iter()
                .map(|variant| {
                    let ty = self.register_type(|this, id| {
                        this.to_be_assigned.insert(id);

                        Type {
                            meta: TypeMeta {
                                // We assign this later.
                                path: TypePath::empty(),
                                attributes: variant.attributes,
                                extra: variant.extra,
                                extra_validation: variant.extra_validation,
                                ..Default::default()
                            },
                            kind: match variant.kind {
                                VariantKind::Explicit(fields)
                                | VariantKind::Flattened(TypeKind::Struct(fields)) => {
                                    TypeKind::EnumVariant {
                                        variant: variant.ident.clone(),
                                        // This gets assigned later.
                                        enum_type: Self::any_type(),
                                        fields,
                                    }
                                }
                                VariantKind::Flattened(type_kind) => type_kind,
                            },
                        }
                    });
                    (variant.ident, ty)
                })
                .collect(),
        )
    }

    pub(crate) fn get_or_register_asset_ref(&mut self, inner: TypeId) -> TypeId {
        if let Some(id) = self.asset_refs.get(&inner) {
            *id
        } else {
            self.register_type(|this, id| {
                this.asset_refs.insert(inner, id);
                let mut ty = Type {
                    meta: TypeMeta {
                        path: TypePath::new(format!("Ref<{}>", this.key_type(inner).meta.path))
                            .expect("Invariant"),
                        traits: this.key_type(inner).meta.traits.clone(),
                        ..Default::default()
                    },
                    kind: TypeKind::Ref(inner),
                };

                this.on_register_type(id, &mut ty);

                ty
            })
        }
    }

    fn on_register_type(&mut self, id: TypeId, ty: &mut Type) {
        if let Some(d) = ty.meta.default.as_mut() {
            d.ty = id;
        }
        for tr in ty.meta.traits.iter() {
            let TypeKind::Trait(types) = &mut self.types[tr.0.0].kind else {
                panic!("Invariant")
            };

            types.insert(id);
        }

        match &ty.kind {
            TypeKind::Enum { variants } => {
                for (variant, variant_ty) in &variants.0 {
                    self.to_be_assigned.remove(variant_ty);
                    self.types[variant_ty.0].meta = TypeMeta {
                                path: ty.meta.path.join(variant),
                                generic_base_type: ty.meta.generic_base_type.map(|generic| {
                                    let generic_id = self.get_or_register_generic_type(
                                        self.key_type(generic).meta.path.join(variant),
                                    );
                                    let TypeKind::Generic(types) = &mut self.types[generic_id.0.0].kind else {
                                        panic!(
                                            "`generic_base_type` pointing to a type that isn't `TypeKind::Generic`"
                                        )
                                    };

                                    types.insert(*variant_ty);

                                    generic_id
                                }),
                                ..ty.meta.clone()
                            };
                    if let TypeKind::EnumVariant {
                        enum_type,
                        variant: v,
                        ..
                    } = &mut self.types[variant_ty.0].kind
                    {
                        *enum_type = id;
                        *v = variant.clone();
                    }
                }
            }
            TypeKind::Or(bitflag) => {
                for variant in &bitflag.variants {
                    self.register_type(|this, variant_id| Type {
                                meta: TypeMeta {
                                    path: ty.meta.path.join(variant),
                                    generic_base_type: ty.meta.generic_base_type.map(|generic| {
                                        let id = this.get_or_register_generic_type(
                                            this.key_type(generic).meta.path.join(variant),
                                        );
                                        let TypeKind::Generic(types) = &mut this.types[id.0.0].kind else {
                                            panic!(
                                                "`generic_base_type` pointing to a type that isn't `TypeKind::Generic`"
                                            )
                                        };

                                        types.insert(variant_id);


                                        id
                                    }),
                                    ..ty.meta.clone()
                                },
                                kind: TypeKind::EnumVariant {
                                    enum_type: id,
                                    fields: Fields::Unit,
                                    variant: variant.clone(),
                                },
                            });
                }
            }
            _ => {}
        }

        if let Some(ty) = ty.meta.generic_base_type {
            let TypeKind::Generic(types) = &mut self.types[ty.0.0].kind else {
                panic!("`generic_base_type` pointing to a type that isn't `TypeKind::Generic`")
            };

            types.insert(id);
        }
    }

    #[must_use]
    pub fn register_dummy_type(&mut self, mut ty: Type) -> TypeId {
        self.register_type(|this, id| {
            this.on_register_type(id, &mut ty);

            ty
        })
    }

    /// Is this type system valid?
    ///
    /// Currently this checks:
    /// - Are there any unassigned registered types?
    /// - If `assert_instanciable` is true then if all `instanciable` types have valid bauble representations.
    pub fn validate(&self, assert_instanciable: bool) -> Result<(), TypeSystemError> {
        if !self.to_be_assigned.is_empty() {
            return Err(TypeSystemError::ToBeAssigned(
                self.to_be_assigned
                    .iter()
                    .map(|ty_id| (*ty_id, self.key_type(*ty_id).meta.path.borrow()))
                    .collect(),
            ));
        }

        if assert_instanciable {
            let mut objects = Vec::new();
            for (i, ty_id) in self
                .iter_type_set(self.key_trait(Self::any_trait()))
                .enumerate()
            {
                let ty = self.key_type(ty_id);
                if !ty.kind.instanciable()
                    || !ty.meta.path.is_writable()
                    || !ty.meta.traits.contains(&self.top_level_trait_dependency)
                {
                    continue;
                }

                let object_path = TypePath::new(format!("{}_{i}", ty.meta.path)).unwrap();

                let Some(value) = self.instantiate(ty_id) else {
                    return Err(TypeSystemError::NotInstantiable {
                        ty_id,
                        ty: ty.meta.path.borrow(),
                    });
                };

                objects.push(crate::Object { object_path, value })
            }

            let source = crate::display_formatted(
                objects.as_slice(),
                self,
                &crate::DisplayConfig {
                    debug_types: true,

                    ..Default::default()
                },
            );

            let mut ctx = crate::BaubleContext::from(self.clone());

            ctx.register_file(TypePath::new("validate").unwrap(), source);

            let (loaded_objects, errors) = ctx.load_all();

            if !errors.is_empty() {
                crate::print_errors(Err::<(), _>(errors), &ctx);

                return Err(TypeSystemError::InstantiableErrors);
            }

            for (a, b) in objects.into_iter().zip(loaded_objects) {
                let unspanned = b.value.into_unspanned();
                if a.value != unspanned {
                    return Err(TypeSystemError::ConstructInequality(a.value, unspanned));
                }
            }
        }

        Ok(())
    }

    pub fn reserve_type_id<'a, T: Bauble<'a, A>, A: BaubleAllocator<'a>>(&mut self) -> TypeId {
        self.type_id::<T, A>().unwrap_or_else(|| {
            self.register_type(|this, id| {
                this.to_be_assigned.insert(id);
                this.type_from_rust.insert(std::any::TypeId::of::<T>(), id);
                Type {
                    meta: TypeMeta::default(),
                    kind: TypeKind::Primitive(Primitive::Any),
                }
            })
        })
    }

    pub fn get_or_register_type<'a, T: Bauble<'a, A>, A: BaubleAllocator<'a>>(&mut self) -> TypeId {
        let id = self.type_id::<T, A>();

        match id {
            Some(id) if self.to_be_assigned.remove(&id) => {
                let mut ty = T::construct_type(self);
                self.on_register_type(id, &mut ty);
                self.types[id.0] = ty;

                id
            }
            Some(id) => id,
            None => self.register_type(|this, id| {
                this.type_from_rust.insert(std::any::TypeId::of::<T>(), id);
                let mut ty = T::construct_type(this);
                this.on_register_type(id, &mut ty);

                ty
            }),
        }
    }

    /// Generics types are used so that users of bauble can use the path.
    ///
    /// For example using `std::option::Option`, and then we're able to infer
    /// the type from where it's used.
    pub fn get_or_register_generic_type(
        &mut self,
        path: TypePath<impl AsRef<str>>,
    ) -> GenericTypeId {
        if let Some(id) = self.generic.get(path.as_str()) {
            if matches!(self.key_type(*id).kind, TypeKind::Generic(_)) {
                GenericTypeId(*id)
            } else {
                panic!("Generic type wasn't mapped to a `TypeKind::Generic`")
            }
        } else {
            GenericTypeId(self.register_type(|this, id| {
                this.generic.insert(path.to_owned(), id);

                Type {
                    meta: TypeMeta {
                        path: path.to_owned(),
                        ..Default::default()
                    },
                    kind: TypeKind::Generic(TypeSet(SealedTypeSet::Certain(Default::default()))),
                }
            }))
        }
    }

    pub fn get_or_register_trait<T: ?Sized + BaubleTrait>(&mut self) -> TraitId {
        let rust_id = std::any::TypeId::of::<T>();
        if let Some(id) = self.type_from_rust.get(&rust_id) {
            if matches!(self.key_type(*id).kind, TypeKind::Trait(_)) {
                TraitId(*id)
            } else {
                panic!("Trait type wasn't mapped to a `TypeKind::Trait`")
            }
        } else {
            TraitId(self.register_type(|this, id| {
                this.type_from_rust.insert(rust_id, id);

                Type {
                    meta: TypeMeta {
                        path: match TypePath::new(T::BAUBLE_PATH) {
                            Ok(path) => path.to_owned(),
                            Err(e) => {
                                panic!(
                                    "Bauble trait `{}`'s path isn't valid: `{}`, err: {e:?}",
                                    std::any::type_name::<T>(),
                                    T::BAUBLE_PATH
                                )
                            }
                        },
                        ..Default::default()
                    },
                    kind: TypeKind::Trait(TypeSet(SealedTypeSet::Certain(Default::default()))),
                }
            }))
        }
    }

    pub fn set_top_level_trait_dependency(&mut self, tr: TraitId) {
        self.top_level_trait_dependency = tr;
    }

    pub fn add_trait_dependency(&mut self, ty: TypeId, tr: TraitId) {
        self.types[ty.0].meta.traits.push(tr);

        let TypeKind::Trait(tr) = &mut self.types[tr.0.0].kind else {
            unreachable!("Invariant");
        };

        tr.insert(ty);
    }

    /// # Panics
    /// Can panic if `TypeId` hasn't been constructed using this `TypeRegistry`.
    pub fn key_type(&self, id: impl Into<TypeId>) -> &Type {
        self.types.get(id.into().0).expect("unknown type id")
    }

    pub fn key_trait(&self, id: TraitId) -> &TypeSet {
        match &self.key_type(id).kind {
            TypeKind::Trait(type_set) => type_set,
            _ => unreachable!("Invariant"),
        }
    }

    pub fn key_generic(&self, id: GenericTypeId) -> &TypeSet {
        match &self.key_type(id).kind {
            TypeKind::Generic(type_set) => type_set,
            _ => unreachable!("Invariant"),
        }
    }

    pub fn get_type_by_id(&self, id: std::any::TypeId) -> Option<&Type> {
        self.type_id_of_std_id(id).map(|id| self.key_type(id))
    }

    pub fn get_type<'a, T: Bauble<'a, A>, A: BaubleAllocator<'a>>(&self) -> Option<&Type> {
        self.type_id::<T, A>().map(|id| self.key_type(id))
    }

    pub fn get_trait<T: ?Sized + BaubleTrait>(&self) -> Option<&Type> {
        self.trait_id::<T>().map(|id| self.key_type(id))
    }

    pub fn iter_type_set<'a>(&self, type_set: &'a TypeSet) -> impl Iterator<Item = TypeId> + 'a {
        match &type_set.0 {
            SealedTypeSet::All => Some((0..self.types.len()).map(TypeId))
                .into_iter()
                .flatten()
                .chain(
                    None::<std::iter::Copied<std::collections::hash_set::Iter<TypeId>>>
                        .into_iter()
                        .flatten(),
                ),
            SealedTypeSet::Certain(hash_set) => None
                .into_iter()
                .flatten()
                .chain(Some(hash_set.iter().copied()).into_iter().flatten()),
        }
    }

    pub fn get_writable_path(&self, ty: TypeId) -> Option<TypePath<&str>> {
        let p = self.key_type(ty).meta.path.borrow();

        if p.is_writable() {
            Some(p)
        } else if let Some(t) = self.key_type(ty).meta.generic_base_type {
            let p = self.key_type(t).meta.path.borrow();
            p.is_writable().then_some(p)
        } else {
            None
        }
    }

    pub fn can_infer_from(&self, output_id: TypeId, input_id: TypeId) -> bool {
        if output_id == input_id {
            return true;
        }
        let target = self.key_type(output_id);
        let input = self.key_type(input_id);

        match (&target.kind, &input.kind) {
            (TypeKind::Primitive(Primitive::Any), _) => true,
            (TypeKind::Transparent(id), _) => self.can_infer_from(*id, input_id),
            (_, TypeKind::EnumVariant { enum_type, .. }) => {
                self.can_infer_from(output_id, *enum_type)
            }
            (TypeKind::Enum { variants }, _) => {
                // Direct references to flattened types are allowed.
                variants
                    .0
                    .values()
                    .any(|output_id| self.can_infer_from(*output_id, input_id))
            }

            (TypeKind::Trait(types), _) => types.contains(input_id),
            (TypeKind::Ref(a), TypeKind::Ref(b)) => self.can_infer_from(*a, *b),
            (TypeKind::Ref(t), _) => self.can_infer_from(*t, input_id),

            (TypeKind::Primitive(a), TypeKind::Primitive(b)) => a == b,

            (_, TypeKind::Generic(types)) => types.contains(output_id),
            _ => false,
        }
    }

    /// Create a value with this type.
    pub fn instantiate(&self, ty_id: TypeId) -> Option<UnspannedVal> {
        let ty = self.key_type(ty_id);

        if let Some(default) = &ty.meta.default {
            return Some(default.clone().with_type(ty_id));
        }

        let construct_unnamed = |fields: &UnnamedFields| {
            fields
                .required
                .iter()
                .map(|f| {
                    if let Some(d) = &f.default {
                        Some(d.clone())
                    } else {
                        self.instantiate(f.id)
                    }
                })
                .collect::<Option<Vec<_>>>()
        };

        let construct_named = |fields: &NamedFields| {
            fields
                .required
                .iter()
                .map(|(s, f)| {
                    Some((
                        s.clone(),
                        if let Some(d) = &f.default {
                            d.clone()
                        } else {
                            self.instantiate(f.id)?
                        },
                    ))
                })
                .collect::<Option<IndexMap<String, UnspannedVal>>>()
        };

        let value = match &ty.kind {
            TypeKind::Tuple(fields) => crate::Value::Tuple(construct_unnamed(fields)?),
            TypeKind::Array(array) => crate::Value::Array(if let Some(l) = array.len {
                vec![self.instantiate(array.ty.id)?; l]
            } else {
                Vec::new()
            }),
            TypeKind::Map(map) => crate::Value::Map(if let Some(l) = map.len {
                // TODO: Is it a problem that the keys will be duplicates?
                vec![
                    (
                        self.instantiate(map.key.id)?,
                        self.instantiate(map.value.id)?
                    );
                    l
                ]
            } else {
                Vec::new()
            }),
            TypeKind::Struct(fields) | TypeKind::EnumVariant { fields, .. } => {
                crate::Value::Struct(match fields {
                    Fields::Unit => crate::FieldsKind::Unit,
                    Fields::Unnamed(fields) => {
                        crate::FieldsKind::Unnamed(construct_unnamed(fields)?)
                    }
                    Fields::Named(fields) => crate::FieldsKind::Named(construct_named(fields)?),
                })
            }
            TypeKind::Enum { variants } => variants.iter().find_map(|(variant, ty)| {
                self.instantiate(ty)
                    .map(|v| crate::Value::Enum(variant.to_owned(), Box::new(v)))
            })?,
            TypeKind::Or(_) => crate::Value::Or(Vec::new()),
            TypeKind::Ref(_) => return None,
            TypeKind::Primitive(primitive) => crate::Value::Primitive(match primitive {
                Primitive::Any => crate::PrimitiveValue::Unit,
                Primitive::Num => crate::PrimitiveValue::Num(rust_decimal::Decimal::ZERO),
                Primitive::Str => crate::PrimitiveValue::Str(String::new()),
                Primitive::Bool => crate::PrimitiveValue::Bool(false),
                Primitive::Unit => crate::PrimitiveValue::Unit,
                Primitive::Raw => crate::PrimitiveValue::Raw(String::new()),
            }),
            TypeKind::Transparent(ty) => {
                let inner = self.key_type(*ty);
                crate::Value::Transparent(Box::new(if let TypeKind::Trait(tr) = &inner.kind {
                    self.iter_type_set(tr).find_map(|ty| self.instantiate(ty))?
                } else {
                    self.instantiate(*ty)?
                }))
            }
            TypeKind::Trait(_) => return None,
            TypeKind::Generic(_) => return None,
        };

        Some(UnspannedVal {
            ty: ty_id,
            value,
            attributes: crate::Attributes::from(construct_named(&ty.meta.attributes)?),
        })
    }
}

pub type ValidationFunction =
    fn(val: &crate::Val, registry: &TypeRegistry) -> Result<(), crate::ConversionError>;

#[derive(Default, Clone, Debug)]
pub struct TypeMeta {
    pub path: TypePath,
    /// If this is `Some` the type is generic.
    pub generic_base_type: Option<GenericTypeId>,
    pub traits: Vec<TraitId>,
    pub default: Option<UnspannedVal>,
    pub nullable: bool,
    /// What attributes the type expects.
    pub attributes: NamedFields,
    /// If this type has any extra invariants that need to be checked.
    pub extra_validation: Option<ValidationFunction>,
    pub extra: IndexMap<String, String>,
}

#[derive(Debug, Clone)]
pub struct FieldType {
    pub id: TypeId,
    pub extra: IndexMap<String, String>,
    pub default: Option<UnspannedVal>,
}

impl From<TypeId> for FieldType {
    fn from(value: TypeId) -> Self {
        Self {
            id: value,
            extra: Default::default(),
            default: None,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Type {
    pub meta: TypeMeta,
    pub kind: TypeKind,
}

#[derive(Default, Clone, Debug)]
pub struct UnnamedFields {
    pub required: Vec<FieldType>,
    pub optional: Vec<FieldType>,
    pub allow_additional: Option<FieldType>,
}

impl UnnamedFields {
    pub fn get(&self, i: usize) -> Option<&FieldType> {
        self.required
            .get(i)
            .or_else(|| self.optional.get(i - self.required.len()))
            .or(self.allow_additional.as_ref())
    }

    pub fn empty() -> Self {
        Self::default()
    }

    pub fn with_required<F: Into<FieldType>>(mut self, iter: impl IntoIterator<Item = F>) -> Self {
        self.required = iter.into_iter().map(|val| val.into()).collect();
        self
    }

    pub fn with_optional<F: Into<FieldType>>(mut self, iter: impl IntoIterator<Item = F>) -> Self {
        self.optional = iter.into_iter().map(|val| val.into()).collect();
        self
    }

    pub fn any() -> Self {
        Self {
            allow_additional: Some(FieldType::from(TypeRegistry::any_type())),
            ..Self::empty()
        }
    }
}
#[derive(Default, Clone, Debug)]
pub struct NamedFields {
    pub required: IndexMap<String, FieldType>,
    pub optional: IndexMap<String, FieldType>,
    pub allow_additional: Option<FieldType>,
}

impl NamedFields {
    pub fn get<'a>(&'a self, ident: &str) -> Option<&'a FieldType> {
        self.required
            .get(ident)
            .or_else(|| self.optional.get(ident))
            .or(self.allow_additional.as_ref())
    }

    pub fn empty() -> Self {
        Self::default()
    }

    pub fn with_required<S: Into<String>, F: Into<FieldType>>(
        mut self,
        iter: impl IntoIterator<Item = (S, F)>,
    ) -> Self {
        self.required = iter
            .into_iter()
            .map(|(key, val)| (key.into(), val.into()))
            .collect();
        self
    }

    pub fn with_optional<S: Into<String>, F: Into<FieldType>>(
        mut self,
        iter: impl IntoIterator<Item = (S, F)>,
    ) -> Self {
        self.optional = iter
            .into_iter()
            .map(|(key, val)| (key.into(), val.into()))
            .collect();
        self
    }

    pub fn with_additional<F: Into<FieldType>>(mut self, f: F) -> Self {
        self.allow_additional = Some(f.into());

        self
    }

    pub fn any() -> Self {
        Self {
            allow_additional: Some(FieldType::from(TypeRegistry::any_type())),
            ..Self::empty()
        }
    }
}

#[derive(Debug, Clone)]
pub enum Fields {
    Unit,
    Unnamed(UnnamedFields),
    Named(NamedFields),
}

#[derive(Debug, Clone)]
pub struct EnumVariants(IndexMap<TypePathElem, TypeId>);

impl EnumVariants {
    pub fn get(&self, variant: TypePathElem<&str>) -> Option<TypeId> {
        self.0.get(&variant).copied()
    }

    pub fn iter(&self) -> impl Iterator<Item = (TypePathElem<&str>, TypeId)> {
        self.0.iter().map(|(key, value)| (key.borrow(), *value))
    }
}

#[derive(Debug, Clone)]
pub struct ArrayType {
    pub ty: FieldType,
    /// None means any size.
    pub len: Option<usize>,
}

#[derive(Debug, Clone)]
pub struct MapType {
    pub key: FieldType,
    pub value: FieldType,
    /// None means any size.
    pub len: Option<usize>,
}

#[derive(Debug, Clone)]
pub struct OrType {
    pub variants: Vec<TypePathElem>,
}

#[derive(Debug, Clone)]
pub enum TypeKind {
    Tuple(UnnamedFields),
    Array(ArrayType),
    Map(MapType),
    Struct(Fields),
    /// Use `TypeRegistry::build_enum` to create this.
    Enum {
        variants: EnumVariants,
    },
    Or(OrType),
    Ref(TypeId),
    Primitive(Primitive),
    Transparent(TypeId),
    #[doc(hidden)]
    EnumVariant {
        variant: TypePathElem,
        enum_type: TypeId,
        fields: Fields,
    },
    #[doc(hidden)]
    Trait(TypeSet),
    #[doc(hidden)]
    Generic(TypeSet),
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(usize)]
pub enum Primitive {
    Any,
    Num,
    Str,
    Bool,
    Unit,
    Raw,
}

impl From<Primitive> for TypeKind {
    fn from(value: Primitive) -> Self {
        TypeKind::Primitive(value)
    }
}

impl TypeKind {
    pub fn instanciable(&self) -> bool {
        match self {
            TypeKind::Tuple(_)
            | TypeKind::Array(_)
            | TypeKind::Map(_)
            | TypeKind::Struct(_)
            | TypeKind::Enum { .. }
            | TypeKind::Or(..)
            | TypeKind::Ref(..)
            | TypeKind::Transparent(..)
            | TypeKind::EnumVariant { .. } => true,
            TypeKind::Trait(_) | TypeKind::Generic(_) => false,
            TypeKind::Primitive(prim) => match prim {
                Primitive::Num
                | Primitive::Str
                | Primitive::Bool
                | Primitive::Unit
                | Primitive::Raw => true,
                Primitive::Any => false,
            },
        }
    }
}
