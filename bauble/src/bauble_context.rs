use indexmap::IndexMap;

use crate::{
    Bauble, BaubleAllocator, BaubleErrors,
    path::{TypePath, TypePathElem},
    types::{TypeId, TypeRegistry},
};

pub type Source = ariadne::Source<String>;

#[derive(Default, Clone, Debug)]
pub struct PathReference {
    pub ty: Option<TypeId>,
    pub asset: Option<(TypeId, TypePath)>,
    pub module: Option<TypePath>,
}

impl PathReference {
    pub fn any(path: TypePath) -> Self {
        Self {
            ty: Some(TypeRegistry::any_type()),
            asset: Some((TypeRegistry::any_type(), path.clone())),
            module: Some(path.clone()),
        }
    }

    pub fn combined(self, other: Self) -> Option<Self> {
        fn xor_option<T>(a: Option<T>, b: Option<T>) -> Option<Option<T>> {
            match (a, b) {
                (Some(_), Some(_)) => None,
                (Some(t), None) | (None, Some(t)) => Some(Some(t)),
                (None, None) => Some(None),
            }
        }

        Some(Self {
            ty: xor_option(self.ty, other.ty)?,
            asset: xor_option(self.asset, other.asset)?,
            module: xor_option(self.module, other.module)?,
        })
    }

    /// Overrides references of `self` with references of `other`, returns true if
    /// anything was overriden.
    pub fn combine_override(&mut self, other: Self) -> bool {
        let mut o = false;
        if other.ty.is_some() {
            o = true;
            self.ty = other.ty;
        }
        if other.asset.is_some() {
            o = true;
            self.asset = other.asset;
        }
        if other.module.is_some() {
            o = true;
            self.module = other.module;
        }
        o
    }
}

pub struct BaubleContextBuilder {
    registry: TypeRegistry,
}

impl Default for BaubleContextBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl BaubleContextBuilder {
    pub fn new() -> Self {
        Self {
            registry: TypeRegistry::new(),
        }
    }

    pub fn register_type<'a, T: Bauble<'a, A>, A: BaubleAllocator<'a>>(&mut self) -> &mut Self {
        self.registry.get_or_register_type::<T, A>();
        self
    }

    pub fn build(self) -> BaubleContext {
        let mut root_node = CtxNode::default();
        for id in self.registry.type_ids() {
            root_node.build_type(id, &self.registry);
        }

        BaubleContext {
            registry: self.registry,
            root_node,
            files: Vec::new(),
        }
    }
}

#[derive(Default, Debug)]
struct CtxNode {
    reference: PathReference,
    source: Option<FileId>,
    children: IndexMap<TypePathElem, CtxNode>,
}

impl CtxNode {
    fn find<R>(&self, ident: TypePathElem<&str>, visit: impl FnOnce(&CtxNode) -> R) -> Option<R> {
        fn find_inner<R, F: FnOnce(&CtxNode) -> R>(
            node: &CtxNode,
            ident: TypePathElem<&str>,
            mut visit: F,
        ) -> Result<R, F> {
            for (name, child) in node.children.iter() {
                if name.borrow() == ident {
                    return Ok(visit(child));
                }

                match find_inner(child, ident, visit) {
                    Ok(val) => return Ok(val),
                    Err(f) => visit = f,
                }
            }

            Err(visit)
        }

        find_inner(self, ident, visit).ok()
    }
    fn walk<R>(&self, path: TypePath<&str>, visit: impl FnOnce(&CtxNode) -> R) -> Option<R> {
        if path.is_empty() {
            Some(visit(self))
        } else {
            let Some((root, rest)) = path.split_start() else {
                unreachable!("We checked that the path wasn't empty")
            };
            self.children
                .get(&root)
                .and_then(|node| node.walk(rest, visit))
        }
    }

    /// Tries to find with `visit`. If `path` doesn't return `Some` when passed to `visit`, we
    /// run `visit` with the parent node and so on.
    ///
    /// Returns the path that we got the result from and `R`.
    ///
    /// Returns None if `path` doesn't exist.
    fn walk_find<'a, R: 'a>(
        &'a self,
        path: TypePath<&str>,
        mut visit: impl FnMut(&'a CtxNode) -> Option<R>,
    ) -> Option<(TypePath, R)> {
        fn walk_find_inner<'a, R: 'a>(
            node: &'a CtxNode,
            path: TypePath<&str>,
            visit: &mut impl FnMut(&'a CtxNode) -> Option<R>,
        ) -> Option<(TypePath, R)> {
            if path.is_empty() {
                Some((TypePath::empty(), visit(node)?))
            } else {
                let Some((root, rest)) = path.split_start() else {
                    unreachable!("We checked that the path wasn't empty")
                };
                let child_node = node.children.get(&root)?;
                match walk_find_inner(child_node, rest, visit) {
                    Some((mut path, r)) => {
                        path.push_start(root.into());

                        Some((path, r))
                    }
                    None => Some((TypePath::empty(), visit(node)?)),
                }
            }
        }

        walk_find_inner(self, path, &mut visit)
    }

    fn walk_mut<R>(
        &mut self,
        path: TypePath<&str>,
        visit: impl FnOnce(&mut CtxNode) -> R,
    ) -> Option<R> {
        if path.is_empty() {
            Some(visit(self))
        } else {
            let Some((root, rest)) = path.split_start() else {
                unreachable!("We checked that the path wasn't empty")
            };
            self.children
                .get_mut(&root)
                .and_then(|node| node.walk_mut(rest, visit))
        }
    }

    fn is_empty(&self) -> bool {
        self.reference.ty.is_none()
            && self.reference.module.is_none()
            && self.reference.asset.is_none()
            && self.children.is_empty()
            && self.source.is_none()
    }

    fn clear_child_assets(&mut self) {
        self.children.retain(|_, node| {
            if node.source.is_some() {
                return true;
            }

            node.clear_child_assets();

            node.reference.asset = None;

            !node.is_empty()
        });
    }

    /// Builds all path elements as modules
    fn build_modules(&mut self, mut path: TypePath, child_path: TypePath<&str>) -> &mut CtxNode {
        self.reference.module = Some(path.clone());
        let Some((child, rest)) = child_path.split_start() else {
            return self;
        };
        path.push(child.into());
        let child = self.children.entry(child.to_owned()).or_default();

        child.build_modules(path, rest)
    }

    /// # Panics
    /// * If `id` isn't from `type_registry`.
    /// * If there are multiple entries at the same path.
    fn build_type(&mut self, id: TypeId, type_registry: &TypeRegistry) {
        let ty = type_registry.key_type(id);

        let Some((module, name)) = ty.meta.path.split_end() else {
            // Types with empty paths aren't added here.
            return;
        };
        let module = self.build_modules(TypePath::empty(), module);
        let node = module.children.entry(name.to_owned()).or_default();
        if let Some(ty) = node.reference.ty
            && ty != id
        {
            panic!("Multiple types with the same path");
        }
        node.reference.ty = Some(id);
    }

    fn build_asset(&mut self, path: TypePath, ty: TypeId) {
        let Some((module, name)) = path.split_end() else {
            // Types with empty paths aren't added here.
            return;
        };

        let module = self.build_modules(TypePath::empty(), module);
        let node = module.children.entry(name.to_owned()).or_default();
        if node.reference.asset.is_some() {
            panic!("Multiple types with the same path");
        }
        node.reference.asset = Some((ty, path));
    }

    fn find_file_id(&self, path: TypePath<&str>) -> Option<FileId> {
        self.walk_find(path, |node| node.source).map(|(_, s)| s)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FileId(usize);

pub struct BaubleContext {
    registry: TypeRegistry,
    root_node: CtxNode,
    files: Vec<(TypePath, Source)>,
}

impl BaubleContext {
    pub fn debug_node(&self) {
        // eprintln!("{:#?}", self.root_node);
    }
    pub fn register_file(&mut self, path: TypePath<&str>, source: impl Into<String>) {
        let node = self.root_node.build_modules(TypePath::empty(), path);
        let id = FileId(self.files.len());
        node.source = Some(id);
        self.files
            .push((path.to_owned(), ariadne::Source::from(source.into())));
    }

    /// Registers an asset. This is done automatically for any objects in a file that gets registered.
    ///
    /// With this method you can expose assets that aren't in bauble.
    pub fn register_asset(&mut self, path: TypePath, ty: TypeId) {
        let ref_ty = self.registry.get_or_register_asset_ref(ty);
        self.root_node.build_type(ref_ty, &self.registry);
        self.root_node.build_asset(path, ref_ty);
    }

    fn file(&self, file: FileId) -> (TypePath<&str>, &Source) {
        let (path, source) = &self.files[file.0];

        (path.borrow(), source)
    }

    fn file_mut(&mut self, file: FileId) -> (TypePath<&str>, &mut Source) {
        let (path, source) = &mut self.files[file.0];

        (path.borrow(), source)
    }

    /// Loads all registered files.
    pub fn load_all(&mut self) -> (Vec<crate::Object>, BaubleErrors) {
        self.reload_files((0..self.files.len()).map(FileId))
    }

    /// Reload all paths, and registers any new files.
    pub fn reload_paths<S0: AsRef<str>, S1: Into<String>>(
        &mut self,
        paths: impl IntoIterator<Item = (TypePath<S0>, S1)>,
    ) -> (Vec<crate::Object>, BaubleErrors) {
        let ids = paths
            .into_iter()
            .map(|(path, source)| match self.get_file_id(path.borrow()) {
                Some(id) => {
                    *self.file_mut(id).1 = Source::from(source.into());
                    id
                }
                None => {
                    self.register_file(path.borrow(), source);
                    self.get_file_id(path.borrow())
                        .expect("We just registered the file")
                }
            })
            .collect::<Vec<_>>();

        self.reload_files(ids)
    }

    /// This clears asset references in any of the file modules.
    fn reload_files<I: IntoIterator<Item = FileId>>(
        &mut self,
        files: I,
    ) -> (Vec<crate::Object>, BaubleErrors)
    where
        I::IntoIter: Clone + ExactSizeIterator,
    {
        let files = files.into_iter();
        // Clear any previous assets that were loaded by these files.
        for file in files.clone() {
            // Need a partial borrow here.
            let (path, _) = &self.files[file.0];
            self.root_node
                .walk_mut(path.borrow(), |node| node.clear_child_assets());
        }

        let mut file_values = Vec::with_capacity(files.len());

        let mut skip = Vec::new();
        // Parse values, and return any errors.
        let mut errors = BaubleErrors::empty();
        for file in files.clone() {
            let values = match crate::parse(file, self) {
                Ok(values) => values,
                Err(err) => {
                    skip.push(file);
                    errors.extend(err);
                    continue;
                }
            };

            file_values.push(values);
        }

        let mut skip_iter = skip.iter().copied().peekable();
        let mut new_skip = Vec::new();

        for (file, values) in files.clone().zip(file_values.iter()).filter(|(file, _)| {
            if skip_iter.peek() == Some(file) {
                skip_iter.next();
                false
            } else {
                true
            }
        }) {
            // Need a partial borrow here.
            let (path, _) = self.file(file);
            let path = path.to_owned();
            if let Err(e) = crate::value::register_assets(path.borrow(), self, [], values) {
                // Skip files that errored on registering.
                new_skip.push(file);
                errors.extend(BaubleErrors::from(e));
            }
        }

        let mut objects = Vec::new();
        let mut skip_a = skip.into_iter().peekable();
        let mut skip_b = new_skip.into_iter().peekable();

        for (file, values) in files.zip(file_values).filter(|(file, _)| {
            if skip_a.peek() == Some(file) {
                skip_a.next();
                false
            } else if skip_b.peek() == Some(file) {
                skip_b.next();
                false
            } else {
                true
            }
        }) {
            match crate::value::convert_values(file, values, &crate::value::Symbols::new(&*self)) {
                Ok(o) => objects.extend(o),
                Err(e) => errors.extend(e),
            }
        }

        (objects, errors)
    }
}

pub trait AssetContext: Sized {
    fn type_registry(&self) -> &TypeRegistry;

    /// Get a reference from `path`.
    fn get_ref(&self, path: TypePath<&str>) -> Option<PathReference>;

    /// Get all the direct child references of `path`.
    fn all_in(&self, path: TypePath<&str>) -> Option<Vec<(TypePathElem, PathReference)>>;

    /// If there is only one valid `Reference` with the identifier `ident`
    /// somewhere in a child path of `path`, return that.
    fn with_ident(&self, path: TypePath<&str>, ident: TypePathElem<&str>) -> Option<PathReference>;

    /// Get the source associated with a path.
    fn get_file_id(&self, path: TypePath<&str>) -> Option<FileId>;

    fn get_file_path(&self, file: FileId) -> TypePath<&str>;

    fn get_source(&self, type_id: FileId) -> &Source;
}

pub struct AssetContextCache<A>(pub A);

impl<'a, A: AssetContext + 'a> ariadne::Cache<FileId> for AssetContextCache<&'a A> {
    type Storage = String;

    fn fetch(
        &mut self,
        id: &FileId,
    ) -> Result<&ariadne::Source<Self::Storage>, Box<dyn std::fmt::Debug + '_>> {
        Ok(self.0.get_source(*id))
    }

    fn display<'b>(&self, id: &'b FileId) -> Option<Box<dyn std::fmt::Display + 'b>> {
        Some(Box::new(self.0.get_file_path(*id).to_string()))
    }
}

impl<T: AssetContext> AssetContext for &T {
    fn type_registry(&self) -> &TypeRegistry {
        AssetContext::type_registry(*self)
    }

    fn get_ref(&self, path: TypePath<&str>) -> Option<PathReference> {
        AssetContext::get_ref(*self, path)
    }

    fn all_in(&self, path: TypePath<&str>) -> Option<Vec<(TypePathElem, PathReference)>> {
        AssetContext::all_in(*self, path)
    }

    fn with_ident(&self, path: TypePath<&str>, ident: TypePathElem<&str>) -> Option<PathReference> {
        AssetContext::with_ident(*self, path, ident)
    }

    fn get_file_id(&self, path: TypePath<&str>) -> Option<FileId> {
        AssetContext::get_file_id(*self, path)
    }

    fn get_file_path(&self, file: FileId) -> TypePath<&str> {
        AssetContext::get_file_path(*self, file)
    }

    fn get_source(&self, file: FileId) -> &Source {
        AssetContext::get_source(*self, file)
    }
}

impl AssetContext for BaubleContext {
    fn type_registry(&self) -> &TypeRegistry {
        &self.registry
    }

    fn get_ref(&self, path: TypePath<&str>) -> Option<PathReference> {
        self.root_node.walk(path, |node| node.reference.clone())
    }

    fn all_in(&self, path: TypePath<&str>) -> Option<Vec<(TypePathElem, PathReference)>> {
        self.root_node.walk(path, |node| {
            node.children
                .iter()
                .map(|(key, child_node)| (key.to_owned(), child_node.reference.clone()))
                .collect()
        })
    }

    fn with_ident(&self, path: TypePath<&str>, ident: TypePathElem<&str>) -> Option<PathReference> {
        self.root_node
            .walk(path, |node| node.find(ident, |node| node.reference.clone()))
            .flatten()
    }

    fn get_file_id(&self, path: TypePath<&str>) -> Option<FileId> {
        self.root_node.find_file_id(path)
    }

    fn get_file_path(&self, file: FileId) -> TypePath<&str> {
        self.files
            .get(file.0)
            .expect("FileId was invalid")
            .0
            .borrow()
    }

    fn get_source(&self, file: FileId) -> &Source {
        &self.files.get(file.0).expect("FileId was invalid").1
    }
}

/*
#[derive(Clone)]
pub struct AllowAnyPath {
    pub src: Source,
}

impl AssetContext for AllowAnyPath {
    fn type_id<T: for<'a> Bauble<'a> + std::any::Any>(&self) -> Option<TypeId> {
        None
    }

    fn key_type(&self, id: TypeId) -> &Type {
        todo!()
    }

    fn trait_id<T: for<'a> Bauble<'a> + std::any::Any>(&self) -> Option<TraitId> {
        todo!()
    }

    fn key_trait(&self, id: TraitId) -> &Trait {
        todo!()
    }

    fn get_ref(&self, path: TypePath<&str>) -> Option<PathReference> {
        Some(PathReference::any(path.to_owned()))
    }

    fn all_in(&self, _path: TypePath<&str>) -> Option<Vec<(TypePathElem, PathReference)>> {
        None
    }

    fn with_ident(
        &self,
        _path: TypePath<&str>,
        ident: TypePathElem<&str>,
    ) -> Option<PathReference> {
        None
    }

    fn get_source(&self, _path: TypePath<&str>) -> Option<&Source> {
        Some(&self.src)
    }
}
*/
