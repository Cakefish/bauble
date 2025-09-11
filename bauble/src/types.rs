//! Bauble is a typed format. This means that Bauble will be able to extract type information from the
//! [`BaubleContext`](crate::BaubleContext) and the parsed source files.
//!
//! The typed nature of Bauble brings many benefits such as improved error messages, allowing custom values,
//! type-checked values and gives you greater flexibility to add your own custom validation steps for a
//! type which implements [`Bauble`](crate::Bauble).

use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
    hash::Hash,
    ptr::{DynMetadata, Pointee},
};

#[allow(missing_docs)]
pub mod path;

use indexmap::IndexMap;
use path::{TypePath, TypePathElem};

use crate::{value::UnspannedVal, AdditionalUnspannedObjects, Bauble, BaubleAllocator};

#[allow(missing_docs)]
pub type Extra = IndexMap<String, String>;

/// A trait that can be represented within a bauble context.
pub trait BaubleTrait: Pointee<Metadata = DynMetadata<Self>> + 'static {
    /// The path of the trait used by Bauble when parsing.
    const BAUBLE_PATH: &'static str;
}

impl BaubleTrait for dyn std::any::Any {
    const BAUBLE_PATH: &'static str = "std::Any";
}

impl BaubleTrait for dyn std::fmt::Debug {
    const BAUBLE_PATH: &'static str = "std::Debug";
}

/// A [`TypeId`] represents a type registed by a Bauble [`TypeRegistry`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TypeId(usize);

impl TypeId {
    /// Gets the usize representation of the ID.
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

/// A [`GenericTypeId`] represents a generic type registed by a Bauble [`TypeRegistry`].
///
/// We maintain the invariant that the type is kind `TypeKind::Generic`
#[allow(missing_docs)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct GenericTypeId(TypeId);

/// A [`TraitId`] represents a trait registed by a Bauble [`TypeRegistry`].
///
/// We maintain the invariant that the type is kind `TypeKind::Trait`
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TraitId(TypeId);

#[derive(Clone, Debug)]
enum SealedTypeSet {
    All,
    Certain(HashSet<TypeId>),
}

/// Represents a set of types impelemnting a specific trait.
#[derive(Debug, Clone)]
pub struct TypeSet(SealedTypeSet);

impl TypeSet {
    #[allow(missing_docs)]
    pub fn insert(&mut self, ty: TypeId) -> bool {
        match &mut self.0 {
            SealedTypeSet::All => false,
            SealedTypeSet::Certain(set) => set.insert(ty),
        }
    }

    #[allow(missing_docs)]
    pub fn contains(&self, ty: TypeId) -> bool {
        match &self.0 {
            SealedTypeSet::All => true,
            SealedTypeSet::Certain(set) => set.contains(&ty),
        }
    }
}

/// A registry for tracking all registered types and traits inside of a [`BaubleContext`](crate::BaubleContext).
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

#[allow(missing_docs)]
pub enum VariantKind {
    Flattened(TypeKind),
    Explicit(Fields),
}

/// A variant usable by an enum in Bauble used for [`TypeRegistry::build_enum`].
pub struct Variant {
    /// The identifier of the variant.
    pub ident: TypePathElem,
    #[allow(missing_docs)]
    pub kind: VariantKind,
    /// Fields in the form of attributes on the variant.
    pub attributes: NamedFields,
    /// Additional validation to perform during parsing.
    pub extra_validation: Option<ValidationFunction>,
    /// Extra data attached by the user to the variant.
    pub extra: Extra,
    /// Function that produces the default value to be assigned to this if there's a `default` value.
    pub default: Option<DefaultFunction>,
}

impl Variant {
    /// Creates a non-flattened variant.
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

    /// Creates a flattened variant.
    /// A flattened variant does not need its name to be explicitly written when creating it.
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

    #[allow(missing_docs)]
    pub fn with_attributes(mut self, attributes: NamedFields) -> Self {
        self.attributes = attributes;
        self
    }

    #[allow(missing_docs)]
    pub fn with_extra(mut self, extra: Extra) -> Self {
        self.extra = extra;
        self
    }

    #[allow(missing_docs)]
    pub fn with_validation(mut self, validation: ValidationFunction) -> Self {
        self.extra_validation = Some(validation);
        self
    }

    #[allow(missing_docs)]
    pub fn with_default(mut self, f: DefaultFunction) -> Self {
        self.default = Some(f);
        self
    }
}

/// An error that occured within the Bauble context's type-system during [`TypeRegister::validate`].
#[allow(missing_docs)]
#[derive(Debug)]
pub enum TypeSystemError<'a> {
    ToBeAssigned(Vec<(TypeId, TypePath<&'a str>)>),
    NotInstantiable {
        ty_id: TypeId,
        ty: TypePath<&'a str>,
    },
    InstantiableErrors,
    ConstructInequality(String, UnspannedVal, UnspannedVal),
    MissingObjects {
        instantiated_missing: Vec<TypePath>,
        loaded_unknown: Vec<TypePath>,
    },
}

impl Display for TypeSystemError<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeSystemError::ToBeAssigned(items) => {
                write!(f, "The following types haven't been assigned to ")?;
                for (i, (ty_id, ty)) in items.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "`{ty}` ({ty_id:?})")?;
                }

                Ok(())
            }
            TypeSystemError::NotInstantiable { ty_id, ty } => write!(
                f,
                "The type `{ty}` ({ty_id:?}) is expected to be instantiable, but it isn't."
            ),
            TypeSystemError::InstantiableErrors => write!(
                f,
                "Errors while trying to read default instantiated objects"
            ),
            TypeSystemError::ConstructInequality(s, a, b) => {
                write!(
                    f,
                    "The constructed instantiated type, and the value read from the instantiated \
                    value formatted as text are not equal.\nBauble:\n{s}\n\nInstantiated: {a:#?}\nRead: {b:#?}"
                )
            }
            TypeSystemError::MissingObjects {
                instantiated_missing,
                loaded_unknown,
            } => write!(
                f,
                "There were missing and/or unknown objects.\nMissing: {instantiated_missing:?}\nUnknown: {loaded_unknown:?}"
            ),
        }
    }
}

impl TypeRegistry {
    /// This is not performant and should not be exposed API, it is used for tests.
    #[doc(hidden)]
    pub fn find_rust_type(&self, ty: TypeId) -> Option<std::any::TypeId> {
        self.type_from_rust
            .iter()
            .find(|(_, t)| **t == ty)
            .map(|(t, _)| *t)
    }

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
        this.types[any_trait.0 .0].kind = TypeKind::Trait(TypeSet(SealedTypeSet::All));

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

    /// If a type implements the required top-level trait.
    pub fn impls_top_level_trait(&self, id: TypeId) -> bool {
        self.key_trait(self.top_level_trait_dependency).contains(id)
    }

    /// The trait that's expected for all top-level bauble assets to have.
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

    /// Return the type ID of the primitive.
    pub fn primitive_type(&self, primitive: Primitive) -> TypeId {
        self.primitive_types[primitive as usize]
    }

    /// Checks if a type is a primitive type.
    pub fn is_primitive_type(&self, id: TypeId) -> bool {
        self.primitive_types.contains(&id)
    }

    /// Retrieve the Bauble type ID from the type ID generated by Rust.
    pub fn type_id_of_std_id(&self, id: std::any::TypeId) -> Option<TypeId> {
        self.type_from_rust.get(&id).copied()
    }

    /// Return the type ID from `T` if `T` has been registered.
    pub fn type_id<'a, T: Bauble<'a, A>, A: BaubleAllocator<'a>>(&self) -> Option<TypeId> {
        self.type_id_of_std_id(std::any::TypeId::of::<T>())
    }

    /// Return the trait ID based on `T` where `T` derives [`BaubleTrait`].
    pub fn trait_id<T: ?Sized + BaubleTrait>(&self) -> Option<TraitId> {
        self.type_id_of_std_id(std::any::TypeId::of::<T>())
            .map(TraitId)
    }

    /// Iterate over all type IDs.
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
                                default: variant.default,
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
        for tr in ty.meta.traits.iter() {
            let TypeKind::Trait(types) = &mut self.types[tr.0 .0].kind else {
                panic!("Invariant")
            };

            types.insert(id);
        }

        match &ty.kind {
            TypeKind::Enum { variants } => {
                for (variant, variant_ty) in &variants.0 {
                    self.to_be_assigned.remove(variant_ty);
                    self.types[variant_ty.0].meta.path = ty.meta.path.join(variant);
                    self.types[variant_ty.0].meta.generic_base_type = ty.meta.generic_base_type.map(|generic| {
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
                    });

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
            let TypeKind::Generic(types) = &mut self.types[ty.0 .0].kind else {
                panic!("`generic_base_type` pointing to a type that isn't `TypeKind::Generic`")
            };

            types.insert(id);
        }
    }

    /// Makes it possible to register a type which is not represented in Rust.
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
        let file = TypePath::new("validate").unwrap();

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

                let object_name =
                    TypePathElem::new(format!("{}_{i}", ty.meta.path.get_end().unwrap().1))
                        .unwrap();

                let object_path = file.join(&object_name);

                let mut additonal = AdditionalUnspannedObjects::new(file, object_name.borrow());

                let Some(value) = self.instantiate(ty_id, &mut additonal) else {
                    return Err(TypeSystemError::NotInstantiable {
                        ty_id,
                        ty: ty.meta.path.borrow(),
                    });
                };

                for (name, value) in additonal.into_objects() {
                    objects.push(crate::Object {
                        object_path: file.join(&name),
                        value,
                    })
                }

                objects.push(crate::Object { object_path, value })
            }

            // Check that instantiated objects match after being serialized to bauble text and
            // parsed.
            //
            // Changes in sub-asset paths are specifically ignored, only the content of the
            // sub-assets must match.

            let source = crate::display_formatted(
                objects.as_slice(),
                self,
                &crate::DisplayConfig {
                    debug_types: true,

                    ..Default::default()
                },
            );

            let mut ctx = crate::BaubleContext::from(self.clone());

            ctx.register_file(file, source.clone());

            let (loaded_objects, errors) = ctx.load_all();

            if !errors.is_empty() {
                crate::print_errors(Err::<(), _>(errors), &ctx);

                return Err(TypeSystemError::InstantiableErrors);
            }

            let instantiated_object_map: HashMap<_, _> = objects
                .into_iter()
                .map(|obj| (obj.object_path, obj.value))
                .collect();

            let loaded_object_map: HashMap<_, _> = loaded_objects
                .into_iter()
                .map(|obj| {
                    (
                        obj.object_path,
                        (obj.value.value.span, obj.value.into_unspanned()),
                    )
                })
                .collect();

            let mut missing_objects = Vec::new();

            /// Compare two objects and recursively compare their sub-objects (aka sub-assets)
            /// while ignoring differences in the paths that refer to those sub-objects (instead
            /// checking that the values in the sub-objects are indentical).
            fn compare_objects<'a>(
                src: &str,
                instantiated: &UnspannedVal,
                loaded: &UnspannedVal,
                inst_map: &HashMap<TypePath, UnspannedVal>,
                loaded_map: &HashMap<TypePath, (crate::Span, UnspannedVal)>,
            ) -> Result<(), TypeSystemError<'a>> {
                let inquality_err = || {
                    TypeSystemError::ConstructInequality(
                        src.to_string(),
                        instantiated.clone(),
                        loaded.clone(),
                    )
                };

                instantiated.attributes.iter().try_for_each(|(n, a)| {
                    match loaded.attributes.get(n) {
                        Some((_, b)) => compare_objects(src, a, b, inst_map, loaded_map),
                        None => Err(inquality_err()),
                    }
                })?;

                match (&instantiated.value, &loaded.value) {
                    (crate::Value::Ref(a), crate::Value::Ref(b)) => {
                        // Not being writable means this is a sub-asset, so compare the sub assets
                        // rather than the paths to them.
                        //
                        // Note, this means object comparison will pass even when the paths to sub
                        // assets change.
                        if !a.is_writable() {
                            let a = inst_map.get(a).unwrap();
                            let (_, b) = loaded_map.get(b).unwrap();
                            compare_objects(src, a, b, inst_map, loaded_map)?;
                        } else if a != b {
                            return Err(inquality_err());
                        }
                    }
                    (crate::Value::Tuple(a), crate::Value::Tuple(b))
                    | (crate::Value::Array(a), crate::Value::Array(b))
                    | (
                        crate::Value::Struct(crate::FieldsKind::Unnamed(a)),
                        crate::Value::Struct(crate::FieldsKind::Unnamed(b)),
                    ) => {
                        if a.len() != b.len() {
                            return Err(inquality_err());
                        } else if let Some(err) = a.iter().zip(b.iter()).find_map(|(a, b)| {
                            compare_objects(src, a, b, inst_map, loaded_map).err()
                        }) {
                            return Err(err);
                        }
                    }
                    (crate::Value::Map(a), crate::Value::Map(b)) => {
                        if a.len() != b.len() {
                            return Err(inquality_err());
                        } else if let Some(err) =
                            a.iter().zip(b.iter()).find_map(|((k_a, v_a), (k_b, v_b))| {
                                compare_objects(src, k_a, k_b, inst_map, loaded_map)
                                    .err()
                                    .or_else(|| {
                                        compare_objects(src, v_a, v_b, inst_map, loaded_map).err()
                                    })
                            })
                        {
                            return Err(err);
                        }
                    }
                    (
                        crate::Value::Struct(crate::FieldsKind::Unit),
                        crate::Value::Struct(crate::FieldsKind::Unit),
                    ) => {}
                    (
                        crate::Value::Struct(crate::FieldsKind::Named(a)),
                        crate::Value::Struct(crate::FieldsKind::Named(b)),
                    ) => {
                        if a.len() != b.len() {
                            return Err(inquality_err());
                        } else if let Some(err) = a.iter().find_map(|(n, a)| match b.get(n) {
                            Some(b) => compare_objects(src, a, b, inst_map, loaded_map).err(),
                            None => Some(inquality_err()),
                        }) {
                            return Err(err);
                        }
                    }
                    (crate::Value::Or(a), crate::Value::Or(b)) => {
                        if a != b {
                            return Err(inquality_err());
                        }
                    }
                    (crate::Value::Primitive(a), crate::Value::Primitive(b)) => {
                        if a != b {
                            return Err(inquality_err());
                        }
                    }
                    (crate::Value::Transparent(a), crate::Value::Transparent(b)) => {
                        compare_objects(src, a, b, inst_map, loaded_map)?;
                    }
                    (crate::Value::Enum(n_a, a), crate::Value::Enum(n_b, b)) => {
                        if n_a != n_b {
                            return Err(inquality_err());
                        }

                        compare_objects(src, a, b, inst_map, loaded_map)?;
                    }
                    _ => {
                        return Err(inquality_err());
                    }
                };

                Ok(())
            }

            for (s, a, b) in instantiated_object_map.iter().filter_map(|(k, a)| {
                if !k.is_writable() {
                    // Don't compare sub-assets, they will be compared by recursion in `compare_objects`
                    None
                } else if let Some((span, b)) = loaded_object_map.get(k) {
                    Some((*span, a, b))
                } else {
                    missing_objects.push(k.clone());
                    None
                }
            }) {
                let s: String = source.chars().skip(s.start).take(s.end - s.start).collect();

                compare_objects(&s, a, b, &instantiated_object_map, &loaded_object_map)?;
            }

            let unknown_objects: Vec<_> = loaded_object_map
                .into_keys()
                // `k.is_writable()` indicates that this is not a sub-asset, `compare_objects`
                // handles checking for those so we don't produce an error if their paths change.
                .filter(|k| !instantiated_object_map.contains_key(k) && k.is_writable())
                .collect();

            if !missing_objects.is_empty() || !unknown_objects.is_empty() {
                return Err(TypeSystemError::MissingObjects {
                    instantiated_missing: missing_objects,
                    loaded_unknown: unknown_objects,
                });
            }
        }

        Ok(())
    }

    /// Reserve an ID for a type which is not yet fully registered.
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

    /// Register `T` if it is not registerted already, then get the type ID for `T`.
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

    /// Register `T` if it is not registerted already, then get the trait ID for `T`.
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

    /// Sets the trait all top-level assets are expected to have. By default this is the any trait.
    pub fn set_top_level_trait_dependency(&mut self, tr: TraitId) {
        self.top_level_trait_dependency = tr;
    }

    /// Registers `ty` as implementing `tr`.
    pub fn add_trait_dependency(&mut self, ty: TypeId, tr: TraitId) {
        self.types[ty.0].meta.traits.push(tr);

        let TypeKind::Trait(tr) = &mut self.types[tr.0 .0].kind else {
            unreachable!("Invariant");
        };

        tr.insert(ty);
    }

    /// Retrieves a type, panicking if it doesn't exist.
    ///
    /// # Panics
    /// Can panic if `TypeId` hasn't been constructed using this `TypeRegistry`.
    pub fn key_type(&self, id: impl Into<TypeId>) -> &Type {
        self.types.get(id.into().0).expect("unknown type id")
    }

    /// Retrieves a trait, panicking if it doesn't exist.
    ///
    /// # Panics
    /// Can panic if `TraitId` hasn't been constructed using this `TypeRegistry`.
    pub fn key_trait(&self, id: TraitId) -> &TypeSet {
        match &self.key_type(id).kind {
            TypeKind::Trait(type_set) => type_set,
            _ => unreachable!("Invariant"),
        }
    }

    /// Retrieves a generic type, panicking if it doesn't exist.
    ///
    /// # Panics
    /// Can panic if `GenericTypeId` hasn't been constructed using this `TypeRegistry`.
    pub fn key_generic(&self, id: GenericTypeId) -> &TypeSet {
        match &self.key_type(id).kind {
            TypeKind::Generic(type_set) => type_set,
            _ => unreachable!("Invariant"),
        }
    }

    /// Get the type information in Bauble from a Rust generated type ID, if the type with the ID `id` has been registered.
    pub fn get_type_by_id(&self, id: std::any::TypeId) -> Option<&Type> {
        self.type_id_of_std_id(id).map(|id| self.key_type(id))
    }

    /// Get the type information of `T` in Bauble, if the type `T` has been registered.
    pub fn get_type<'a, T: Bauble<'a, A>, A: BaubleAllocator<'a>>(&self) -> Option<&Type> {
        self.type_id::<T, A>().map(|id| self.key_type(id))
    }

    /// Get a trait using the generic `dyn Trait`.
    pub fn get_trait<T: ?Sized + BaubleTrait>(&self) -> Option<&Type> {
        self.trait_id::<T>().map(|id| self.key_type(id))
    }

    /// Iterates the type set for all of its types.
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

    /// Gets the writeable path of a certain path.
    ///
    /// If this type is generic and its path isn't writable this will return the generic types path.
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

    /// If the output type `output_id` can be inferred from the input type `input_id`.
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

    /// Create the default value of this type.
    pub fn instantiate(
        &self,
        ty_id: TypeId,
        additional_objects: &mut AdditionalUnspannedObjects,
    ) -> Option<UnspannedVal> {
        let ty = self.key_type(ty_id);

        if let Some(default) = &ty.meta.default {
            return Some(default(additional_objects, self, ty_id).with_type(ty_id));
        }

        let construct_unnamed =
            |fields: &UnnamedFields, additional_objects: &mut AdditionalUnspannedObjects| {
                fields
                    .required
                    .iter()
                    .map(|f| {
                        if let Some(d) = &f.default {
                            Some(d.clone())
                        } else {
                            self.instantiate(f.id, additional_objects)
                        }
                    })
                    .collect::<Option<Vec<_>>>()
            };

        let construct_named =
            |fields: &NamedFields, additional_objects: &mut AdditionalUnspannedObjects| {
                fields
                    .required
                    .iter()
                    .map(|(s, f)| {
                        Some((
                            s.clone(),
                            if let Some(d) = &f.default {
                                d.clone()
                            } else {
                                self.instantiate(f.id, additional_objects)?
                            },
                        ))
                    })
                    .collect::<Option<IndexMap<String, UnspannedVal>>>()
            };

        let value = match &ty.kind {
            TypeKind::Tuple(fields) => {
                crate::Value::Tuple(construct_unnamed(fields, additional_objects)?)
            }
            TypeKind::Array(array) => crate::Value::Array(if let Some(l) = array.len {
                vec![self.instantiate(array.ty.id, additional_objects)?; l]
            } else {
                Vec::new()
            }),
            TypeKind::Map(map) => crate::Value::Map(if let Some(l) = map.len {
                // TODO: Is it a problem that the keys will be duplicates?
                vec![
                    (
                        self.instantiate(map.key.id, additional_objects)?,
                        self.instantiate(map.value.id, additional_objects)?
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
                        crate::FieldsKind::Unnamed(construct_unnamed(fields, additional_objects)?)
                    }
                    Fields::Named(fields) => {
                        crate::FieldsKind::Named(construct_named(fields, additional_objects)?)
                    }
                })
            }
            TypeKind::Enum { variants } => variants.iter().find_map(|(variant, ty)| {
                self.instantiate(ty, additional_objects)
                    .map(|v| crate::Value::Enum(variant.to_owned(), Box::new(v)))
            })?,
            TypeKind::Or(_) => crate::Value::Or(Vec::new()),
            TypeKind::Ref(inner) => additional_objects.in_type(*inner, |additional_objects| {
                self.instantiate(*inner, additional_objects)
                    .map(|v| additional_objects.add_object(v))
            })?,
            TypeKind::Primitive(primitive) => crate::Value::Primitive(match primitive {
                Primitive::Any => crate::PrimitiveValue::Unit,
                Primitive::Num => crate::PrimitiveValue::Num(rust_decimal::Decimal::ZERO),
                Primitive::Str => crate::PrimitiveValue::Str(String::new()),
                Primitive::Bool => crate::PrimitiveValue::Bool(false),
                Primitive::Unit => crate::PrimitiveValue::Unit,
                // We have no idea at this point what these should look like since it's user defined.
                Primitive::Raw => return None,
            }),
            TypeKind::Transparent(ty) => {
                let inner = self.key_type(*ty);
                crate::Value::Transparent(Box::new(if let TypeKind::Trait(tr) = &inner.kind {
                    self.iter_type_set(tr)
                        .find_map(|ty| self.instantiate(ty, additional_objects))?
                } else {
                    self.instantiate(*ty, additional_objects)?
                }))
            }
            TypeKind::Trait(tr) => {
                let mut v: Vec<_> = self.iter_type_set(tr).collect();
                v.sort_unstable_by(|a, b| {
                    self.key_type(*a)
                        .meta
                        .path
                        .cmp(&self.key_type(*b).meta.path)
                });
                return v
                    .into_iter()
                    .find_map(|t| self.instantiate(t, additional_objects));
            }
            TypeKind::Generic(_) => return None,
        };

        Some(UnspannedVal {
            ty: ty_id,
            value,
            attributes: crate::Attributes::from(construct_named(
                &ty.meta.attributes,
                additional_objects,
            )?),
        })
    }
}

/// The function type for the validation function for [`TypeMeta`].
pub type ValidationFunction =
    fn(val: &crate::Val, registry: &TypeRegistry) -> Result<(), crate::ConversionError>;

/// Function that creates a instance of the default value. Stored in [`TypeMeta`].
///
/// * `&mut AdditionalUnspannedObjects` allows creating sub-assets if the new value needs to
///   reference sub-assets.
/// * `&TypeRegistry` allows calling [`TypeRegistry::instantiate`] to create new default instances
///   of contained types and is used to get type information of contained types.
/// * `TypeId` is the ID of the type. This allows the function to retrieve information about the
///   current type using the `TypeRegistry` parameter, such as type information about
///   fields/variants that are needed to instantiate them.
pub type DefaultFunction =
    fn(&mut AdditionalUnspannedObjects, &TypeRegistry, TypeId) -> UnspannedVal;

/// Meta information on a type registered within a Bauble context.
#[derive(Default, Clone, Debug)]
pub struct TypeMeta {
    /// The path to the type.
    pub path: TypePath,
    /// If this is `Some` the type is generic.
    pub generic_base_type: Option<GenericTypeId>,
    /// The traits implemented by the type.
    pub traits: Vec<TraitId>,
    /// Optional function to create a default value of the type.
    pub default: Option<DefaultFunction>,
    /// What attributes the type expects.
    pub attributes: NamedFields,
    /// If this type has any extra invariants that need to be checked.
    pub extra_validation: Option<ValidationFunction>,
    /// Extra data attached by the user to the type.
    pub extra: Extra,
}

/// A type on a field inside of Bauble.
#[allow(missing_docs)]
#[derive(Debug, Clone)]
pub struct FieldType {
    pub id: TypeId,
    /// Extra data attached by the user to the field.
    pub extra: Extra,
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

/// A Bauble registered type.
#[allow(missing_docs)]
#[derive(Clone, Debug)]
pub struct Type {
    pub meta: TypeMeta,
    pub kind: TypeKind,
}

/// Unnamed fields in a Bauble type.
#[derive(Default, Clone, Debug)]
pub struct UnnamedFields {
    /// Fields that must be specified.
    pub required: Vec<FieldType>,
    /// Optional fields, such as those specified by attributes with default values.
    pub optional: Vec<FieldType>,
    /// If this is some, it allows any amount of that field type following the last
    /// defined required/optional field.
    pub allow_additional: Option<FieldType>,
}

impl UnnamedFields {
    /// Get the type of field with the index `i`.
    pub fn get(&self, i: usize) -> Option<&FieldType> {
        self.required
            .get(i)
            .or_else(|| self.optional.get(i - self.required.len()))
            .or(self.allow_additional.as_ref())
    }

    /// Creates an empty set of unnamed fields.
    pub fn empty() -> Self {
        Self::default()
    }

    /// Specify a set of fields which always have to be assigned a value.
    ///
    /// This will overwrite the previously set required fields.
    pub fn with_required<F: Into<FieldType>>(mut self, iter: impl IntoIterator<Item = F>) -> Self {
        self.required = iter.into_iter().map(|val| val.into()).collect();
        self
    }

    /// Specify a set of fields which may optionally be assigned a value.
    ///
    /// This will overwrite the previously set optional fields.
    pub fn with_optional<F: Into<FieldType>>(mut self, iter: impl IntoIterator<Item = F>) -> Self {
        self.optional = iter.into_iter().map(|val| val.into()).collect();
        self
    }

    /// An `UnnamedFields` to allow any amount of fields of any type.
    pub fn any() -> Self {
        Self {
            allow_additional: Some(FieldType::from(TypeRegistry::any_type())),
            ..Self::empty()
        }
    }
}
/// Named fields in a Bauble type.
#[derive(Default, Clone, Debug)]
pub struct NamedFields {
    /// Fields that must be specified.
    pub required: IndexMap<String, FieldType>,
    /// Optional fields, such as those specified by attributes with default values.
    pub optional: IndexMap<String, FieldType>,
    /// If this is some, it allows a field of field names that aren't defined in `required`
    /// or `òptional` as the specified type.
    pub allow_additional: Option<FieldType>,
}

impl NamedFields {
    /// Get the type of field with the identifier `ident`.
    pub fn get<'a>(&'a self, ident: &str) -> Option<&'a FieldType> {
        self.required
            .get(ident)
            .or_else(|| self.optional.get(ident))
            .or(self.allow_additional.as_ref())
    }

    /// Creates an empty set of named fields.
    pub fn empty() -> Self {
        Self::default()
    }

    /// Specify a set of fields which always have to be assigned a value.
    ///
    /// This will overwrite the previously set required fields.
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

    /// Specify a set of fields which may optionally be assigned a value.
    ///
    /// This will overwrite the previously set optional fields.
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

    // TODO(@docs)
    #[allow(missing_docs)]
    pub fn with_additional<F: Into<FieldType>>(mut self, f: F) -> Self {
        self.allow_additional = Some(f.into());

        self
    }

    // TODO(@docs)
    #[allow(missing_docs)]
    pub fn any() -> Self {
        Self {
            allow_additional: Some(FieldType::from(TypeRegistry::any_type())),
            ..Self::empty()
        }
    }

    /// Returns true if this type can't have attributes
    pub fn is_empty(&self) -> bool {
        self.required.is_empty() && self.optional.is_empty() && self.allow_additional.is_none()
    }
}

/// Represents fields on a type in Bauble.
#[allow(missing_docs)]
#[derive(Debug, Clone)]
pub enum Fields {
    Unit,
    Unnamed(UnnamedFields),
    Named(NamedFields),
}

/// Variants of a single enum inside of Bauble.
#[derive(Debug, Clone)]
pub struct EnumVariants(IndexMap<TypePathElem, TypeId>);

impl EnumVariants {
    /// Get the variant based on its identifier.
    pub fn get<Q>(&self, variant: &Q) -> Option<TypeId>
    where
        Q: ?Sized + Hash + indexmap::Equivalent<TypePathElem>,
    {
        self.0.get(variant).copied()
    }

    /// Iterate all variants.
    pub fn iter(&self) -> impl Iterator<Item = (TypePathElem<&str>, TypeId)> {
        self.0.iter().map(|(key, value)| (key.borrow(), *value))
    }
}

/// An array type in Bauble.
#[derive(Debug, Clone)]
pub struct ArrayType {
    #[allow(missing_docs)]
    pub ty: FieldType,
    /// None means any size.
    pub len: Option<usize>,
}

/// A map type in Bauble.
#[allow(missing_docs)]
#[derive(Debug, Clone)]
pub struct MapType {
    pub key: FieldType,
    pub value: FieldType,
    /// None means any size.
    pub len: Option<usize>,
}

/// The type of expressions which allow being changed by the `|` operator in Bauble. Usually this is bitflags.
#[derive(Debug, Clone)]
pub struct OrType {
    #[allow(missing_docs)]
    pub variants: Vec<TypePathElem>,
}

/// An enum covering all the various kinds of types a Bauble value may have.
#[allow(missing_docs)]
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

/// A primitive type in Bauble.
#[allow(missing_docs)]
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
    /// If the type may be instanciated (created) inside of Bauble.
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
