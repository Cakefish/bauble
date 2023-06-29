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

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct TypeInfo {
    pub module: String,
    pub ident: String,
}

impl TypeInfo {
    pub fn simple(s: impl Into<String>) -> Self {
        TypeInfo {
            module: String::new(),
            ident: s.into(),
        }
    }

    pub fn new(module: impl Into<String>, ident: impl Into<String>) -> Self {
        TypeInfo {
            module: module.into(),
            ident: ident.into(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Struct {
    pub type_info: TypeInfo,
    pub kind: DataFieldsKind,
}

#[derive(Debug, Clone)]
pub struct EnumVariant {
    pub enum_type_info: TypeInfo,
    pub variant: String,
    pub kind: DataFieldsKind,
}

#[derive(Debug, Clone)]
pub struct BitField {
    pub type_info: TypeInfo,
    pub variant: String,
}

#[derive(Debug, Clone)]
pub enum TypeKind {
    Struct(Struct),
    EnumVariant(EnumVariant),
    BitField(BitField),
    Any(TypeInfo),
}

#[derive(Debug, Clone)]
pub enum Reference {
    Any(TypeInfo),
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
            Reference::Any(info) => Some(format!("{}::{}", info.module, info.ident)),
            Reference::Specific { asset, .. } => asset,
        }
    }

    pub fn get_module(&self) -> Option<&str> {
        match self {
            Reference::Any(_) => None,
            Reference::Specific { module, .. } => module.as_deref(),
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
    fn get_ref(&self, path: &str) -> Option<Reference>;

    fn all_in(&self, path: &str) -> Option<Vec<(String, Reference)>>;

    fn with_ident(&self, path: &str, ident: &str) -> Option<Reference>;
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
}

#[derive(Clone)]
pub struct OrContext<A: AssetContext, B: AssetContext> {
    a: A,
    b: B,
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
}

#[derive(Clone)]
pub struct NoChecks;

impl AssetContext for NoChecks {
    fn get_ref(&self, path: &str) -> Option<Reference> {
        let x = path.split("::").last().unwrap();
        let path = path.trim_end_matches(x).trim_end_matches("::");
        Some(Reference::Any(TypeInfo::new(path, x)))
    }

    fn all_in(&self, _path: &str) -> Option<Vec<(String, Reference)>> {
        None
    }

    fn with_ident(&self, _path: &str, _ident: &str) -> Option<Reference> {
        None
    }
}
