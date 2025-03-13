use std::{borrow::Cow, fmt::Display};

use crate::ValueKind;

#[derive(Debug, Clone)]
pub enum DataFieldsKind {
    Unit,
    Tuple(Option<usize>),
    Struct(Option<Vec<String>>),
}

impl DataFieldsKind {
    pub fn is_unit(&self) -> bool {
        matches!(self, DataFieldsKind::Unit)
    }

    pub fn is_tuple(&self) -> bool {
        matches!(self, DataFieldsKind::Tuple(_))
    }

    pub fn is_struct(&self) -> bool {
        matches!(self, DataFieldsKind::Struct(_))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OwnedTypeInfo {
    Path {
        module: String,
        ident: String,
        always_ref: bool,
        attributes: Vec<String>,
    },
    Kind(ValueKind),
    Flatten {
        module: String,
        ident: String,
        always_ref: bool,
        types: Vec<OwnedTypeInfo>,
    },
}

impl Display for OwnedTypeInfo {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OwnedTypeInfo::Kind(kind) => write!(f, "{kind}"),
            OwnedTypeInfo::Path { module, ident, .. } => write!(f, "{module}::{ident}"),
            OwnedTypeInfo::Flatten { types, .. } => {
                write!(
                    f,
                    "({})",
                    types
                        .iter()
                        .map(|ty| ty.to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
        }
    }
}

impl OwnedTypeInfo {
    pub fn new(module: impl Into<String>, ident: impl Into<String>) -> Self {
        OwnedTypeInfo::Path {
            module: module.into(),
            ident: ident.into(),
            always_ref: false,
            attributes: Vec::new(),
        }
    }

    pub fn path(&self) -> Option<String> {
        if let OwnedTypeInfo::Path { module, ident, .. }
        | OwnedTypeInfo::Flatten { module, ident, .. } = self
        {
            Some(format!("{module}::{ident}"))
        } else {
            None
        }
    }

    pub fn is_always_ref(&self) -> bool {
        matches!(
            self,
            OwnedTypeInfo::Path {
                always_ref: true,
                ..
            } | OwnedTypeInfo::Flatten {
                always_ref: true,
                ..
            }
        )
    }
}

#[derive(Debug, Eq, PartialEq)]
pub enum TypeInfo<'a> {
    Path {
        module: &'a str,
        ident: &'a str,
        always_ref: bool,
        attributes: &'a [&'a str],
    },
    Kind(ValueKind),
    Flatten {
        module: &'a str,
        ident: &'a str,
        always_ref: bool,

        types: &'a [&'a TypeInfo<'a>],
    },
}

impl<'a> TypeInfo<'a> {
    pub const fn new(module: &'a str, ident: &'a str) -> Self {
        TypeInfo::Path {
            module,
            ident,
            always_ref: false,
            attributes: &[],
        }
    }

    pub const fn with_always_ref(self) -> Self {
        match self {
            TypeInfo::Path {
                module,
                ident,
                attributes,
                ..
            } => TypeInfo::Path {
                module,
                ident,
                always_ref: true,
                attributes,
            },
            TypeInfo::Flatten {
                module,
                ident,
                types,
                ..
            } => TypeInfo::Flatten {
                module,
                ident,
                always_ref: true,
                types,
            },
            s => s,
        }
    }

    pub const fn with_attributes(self, attributes: &'a [&'a str]) -> Self {
        match self {
            TypeInfo::Path {
                module,
                ident,
                always_ref,
                ..
            } => TypeInfo::Path {
                module,
                ident,
                always_ref,
                attributes,
            },
            s => s,
        }
    }

    pub fn to_owned(&self) -> OwnedTypeInfo {
        match self {
            TypeInfo::Path {
                module,
                ident,
                always_ref,
                attributes,
            } => OwnedTypeInfo::Path {
                module: module.to_string(),
                ident: ident.to_string(),
                always_ref: *always_ref,
                attributes: attributes.iter().map(|s| s.to_string()).collect(),
            },
            &TypeInfo::Kind(kind) => OwnedTypeInfo::Kind(kind),
            TypeInfo::Flatten {
                module,
                ident,
                always_ref,
                types,
            } => OwnedTypeInfo::Flatten {
                types: types.iter().map(|&ty| ty.to_owned()).collect(),
                module: module.to_string(),
                ident: ident.to_string(),
                always_ref: *always_ref,
            },
        }
    }

    pub fn contains(&self, other: &OwnedTypeInfo) -> bool {
        match (self, other) {
            (
                TypeInfo::Path { module, ident, .. },
                OwnedTypeInfo::Path {
                    module: m,
                    ident: i,
                    ..
                },
            ) => module == m && ident == i,
            (TypeInfo::Kind(kind), OwnedTypeInfo::Kind(other_kind)) => kind == other_kind,
            (
                TypeInfo::Flatten {
                    types,
                    module,
                    ident,
                    ..
                },
                other,
            ) => {
                (if let OwnedTypeInfo::Path {
                    module: m,
                    ident: i,
                    ..
                } = other
                {
                    module == m && ident == i
                } else {
                    false
                }) || types.iter().any(|ty| ty.contains(other))
            }
            _ => false,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Struct {
    pub type_info: OwnedTypeInfo,
    pub kind: DataFieldsKind,
}

#[derive(Debug, Clone)]
pub struct EnumVariant {
    pub enum_type_info: OwnedTypeInfo,
    pub variant: String,
    pub kind: DataFieldsKind,
}

#[derive(Debug, Clone)]
pub struct BitField {
    pub type_info: OwnedTypeInfo,
    pub variant: String,
}

#[derive(Debug, Clone)]
pub enum TypeKind {
    Struct(Struct),
    EnumVariant(EnumVariant),
    BitField(BitField),
    Any(OwnedTypeInfo),
}

impl TypeKind {
    pub fn type_info(&self) -> OwnedTypeInfo {
        match self {
            TypeKind::Struct(s) => s.type_info.clone(),
            TypeKind::EnumVariant(e) => e.enum_type_info.clone(),
            TypeKind::BitField(b) => b.type_info.clone(),
            TypeKind::Any(t) => t.clone(),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Reference {
    Any(OwnedTypeInfo),
    Specific {
        ty: Option<TypeKind>,
        asset: Option<String>,
        module: Option<String>,
    },
}

impl Default for Reference {
    fn default() -> Self {
        Reference::Specific {
            ty: None,
            asset: None,
            module: None,
        }
    }
}

impl Reference {
    pub fn to_type(self) -> Option<TypeKind> {
        match self {
            Reference::Any(info) => Some(TypeKind::Any(info)),
            Reference::Specific { ty, .. } => ty,
        }
    }

    pub fn to_asset(self) -> Option<String> {
        match self {
            Reference::Any(info) => Some(format!("{info}")),
            Reference::Specific { asset, .. } => asset,
        }
    }

    pub fn get_module(&self) -> Option<Cow<str>> {
        match self {
            Reference::Any(type_info) => match type_info {
                OwnedTypeInfo::Path { module, ident, .. }
                | OwnedTypeInfo::Flatten { module, ident, .. } => {
                    Some(Cow::Owned(format!("{module}::{ident}")))
                }
                OwnedTypeInfo::Kind(_) => None,
            },
            Reference::Specific { module, .. } => module.as_deref().map(Cow::Borrowed),
        }
    }

    pub fn combined(self, other: Reference) -> Option<Reference> {
        fn xor_option<T>(a: Option<T>, b: Option<T>) -> Option<Option<T>> {
            match (a, b) {
                (Some(_), Some(_)) => None,
                (Some(t), None) | (None, Some(t)) => Some(Some(t)),
                (None, None) => Some(None),
            }
        }
        match (self, other) {
            (Reference::Any(_), _) => None,
            (_, Reference::Any(info)) => Some(Reference::Any(info)),
            (
                Reference::Specific { ty, asset, module },
                Reference::Specific {
                    ty: other_ty,
                    asset: other_asset,
                    module: other_module,
                },
            ) => Some(Reference::Specific {
                ty: xor_option(ty, other_ty)?,
                asset: xor_option(asset, other_asset)?,
                module: xor_option(module, other_module)?,
            }),
        }
    }

    pub fn combine_override(&mut self, other: Reference) -> bool {
        let mut overrode = false;
        match (self, other) {
            (this, other @ Reference::Any(_)) => {
                *this = other;
                overrode = true;
            }
            (
                Reference::Specific { ty, asset, module },
                Reference::Specific {
                    ty: other_ty,
                    asset: other_asset,
                    module: other_module,
                },
            ) => {
                if other_ty.is_some() {
                    overrode |= ty.is_some();
                    *ty = other_ty;
                }
                if other_asset.is_some() {
                    overrode |= asset.is_some();
                    *asset = other_asset;
                }
                if other_module.is_some() {
                    overrode |= module.is_some() && *module == other_module;
                    *module = other_module;
                }
            }
            _ => {}
        }
        overrode
    }
}

pub trait AssetContext: Clone {
    /// Get a reference from `path`.
    fn get_ref(&self, path: &str) -> Option<Reference>;

    /// Get all the direct child references of `path`.
    fn all_in(&self, path: &str) -> Option<Vec<(String, Reference)>>;

    /// If there is only one valid `Reference` with the identifier `ident`
    /// somewhere in a child path of `path`, return that.
    fn with_ident(&self, path: &str, ident: &str) -> Option<Reference>;

    fn get_source(&self, path: &str) -> Option<&Source>;
}

pub struct AssetContextCache<A>(pub A);

impl<'a, S: AsRef<str>, A: AssetContext + 'a> ariadne::Cache<S> for AssetContextCache<&'a A> {
    type Storage = String;

    fn fetch(
        &mut self,
        id: &S,
    ) -> Result<&ariadne::Source<Self::Storage>, Box<dyn std::fmt::Debug + '_>> {
        self.0
            .get_source(id.as_ref())
            .ok_or_else(|| Box::new("Path not found") as _)
    }

    fn display<'b>(&self, id: &'b S) -> Option<Box<dyn std::fmt::Display + 'b>> {
        Some(Box::new(id.as_ref()))
    }
}

impl<T: AssetContext> AssetContext for &T {
    fn get_ref(&self, path: &str) -> Option<Reference> {
        (*self).get_ref(path)
    }

    fn all_in(&self, path: &str) -> Option<Vec<(String, Reference)>> {
        (*self).all_in(path)
    }

    fn with_ident(&self, path: &str, ident: &str) -> Option<Reference> {
        (*self).with_ident(path, ident)
    }

    fn get_source(&self, path: &str) -> Option<&Source> {
        (*self).get_source(path)
    }
}

#[derive(Clone)]
pub struct OrContext<A: AssetContext, B: AssetContext> {
    pub a: A,
    pub b: B,
}

impl<A: AssetContext, B: AssetContext> AssetContext for OrContext<A, B> {
    fn get_ref(&self, path: &str) -> Option<Reference> {
        self.a.get_ref(path).or_else(|| self.b.get_ref(path))
    }

    fn all_in(&self, path: &str) -> Option<Vec<(String, Reference)>> {
        self.a.all_in(path).or_else(|| self.b.all_in(path))
    }

    fn with_ident(&self, path: &str, ident: &str) -> Option<Reference> {
        self.a
            .with_ident(path, ident)
            .or_else(|| self.b.with_ident(path, ident))
    }

    fn get_source(&self, path: &str) -> Option<&Source> {
        self.a.get_source(path).or_else(|| self.b.get_source(path))
    }
}

pub type Source = ariadne::Source<String>;

#[derive(Clone)]
pub struct NoChecks {
    pub src: Source,
}

impl AssetContext for NoChecks {
    fn get_ref(&self, path: &str) -> Option<Reference> {
        let x = path.split("::").last().unwrap();
        let path = path.trim_end_matches(x).trim_end_matches("::");
        Some(Reference::Any(OwnedTypeInfo::new(path, x)))
    }

    fn all_in(&self, _path: &str) -> Option<Vec<(String, Reference)>> {
        None
    }

    fn with_ident(&self, _path: &str, _ident: &str) -> Option<Reference> {
        None
    }

    fn get_source(&self, _path: &str) -> Option<&Source> {
        Some(&self.src)
    }
}
