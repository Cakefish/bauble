use indexmap::IndexMap;

use crate::{
    Bauble, BaubleAllocator, BaubleErrors,
    path::{TypePath, TypePathElem},
    types::{BaubleTrait, TypeId, TypeRegistry},
};

#[allow(missing_docs)]
pub type Source = ariadne::Source<String>;

#[derive(Clone, Default)]
struct DefaultUses(IndexMap<TypePathElem, TypePath>);

#[derive(Default, Clone, Debug)]
struct InnerReference {
    ty: Option<TypeId>,
    asset: Option<TypeId>,
    redirect: Option<TypePath>,
}

/// A type containing multiple references generally derived from a path.
#[derive(Default, Clone, Debug)]
pub struct PathReference {
    /// The type referenced by a path.
    pub ty: Option<TypeId>,
    /// The asset (and its path) referenced by the path.
    pub asset: Option<(TypeId, TypePath)>,
    /// If the reference references a module.
    pub module: Option<TypePath>,
}

impl PathReference {
    /// Constructs an empty path reference.
    pub fn empty() -> Self {
        Self {
            ty: None,
            asset: None,
            module: None,
        }
    }

    /// Constructs a path reference referencing the 'any' type.
    pub fn any(path: TypePath) -> Self {
        Self {
            ty: Some(TypeRegistry::any_type()),
            asset: Some((TypeRegistry::any_type(), path.clone())),
            module: Some(path.clone()),
        }
    }

    /// Take the exclusive properties of `self` and `other`, essentially "xor"ing them together by producing
    /// the combined result where each field where both are `Some` are `None`.
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

/// A builder used to create a [`BaubleContext`].
///
/// The builder is mainly useful to register various types into the context.
#[derive(Clone)]
pub struct BaubleContextBuilder {
    registry: TypeRegistry,
    default_uses: DefaultUses,
}

impl Default for BaubleContextBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl BaubleContextBuilder {
    #[allow(missing_docs)]
    pub fn new() -> Self {
        let mut this = Self {
            registry: TypeRegistry::new(),
            default_uses: DefaultUses::default(),
        };

        this.with_default_use(
            TypePathElem::new("Some").unwrap().to_owned(),
            TypePath::new("std::Option::Some").unwrap().to_owned(),
        )
        .with_default_use(
            TypePathElem::new("None").unwrap().to_owned(),
            TypePath::new("std::Option::None").unwrap().to_owned(),
        );
        this
    }

    /// Register type `T` into the context if it is not already registered.
    pub fn register_type<'a, T: Bauble<'a, A>, A: BaubleAllocator<'a>>(&mut self) -> &mut Self {
        self.get_or_register_type::<T, A>();
        self
    }

    /// Register type `T` into the context if it is not already registered, then return its associated ID.
    pub fn get_or_register_type<'a, T: Bauble<'a, A>, A: BaubleAllocator<'a>>(&mut self) -> TypeId {
        self.registry.get_or_register_type::<T, A>()
    }

    #[allow(missing_docs)]
    pub fn type_registry(&mut self) -> &mut TypeRegistry {
        &mut self.registry
    }

    /// Register trait described by `T` where T implements [`BaubleTrait`] for the type associated with the id `ty`.
    pub fn add_trait_for_type<T: ?Sized + BaubleTrait>(&mut self, ty: TypeId) -> &mut Self {
        let tr = self.registry.get_or_register_trait::<T>();
        self.registry.add_trait_dependency(ty, tr);

        self
    }

    #[allow(missing_docs)]
    pub fn set_top_level_trait_requirement<T: ?Sized + BaubleTrait>(&mut self) -> &mut Self {
        let tr = self.registry.get_or_register_trait::<T>();
        self.registry.set_top_level_trait_dependency(tr);

        self
    }

    /// Includes an implicit `use` prelude into parsed Bauble files.
    pub fn with_default_use(&mut self, ident: TypePathElem, path: TypePath) -> &mut Self {
        self.default_uses.0.insert(ident, path);
        self
    }

    // TODO: documentation
    #[allow(missing_docs)]
    /// # Panics
    ///
    /// Can panic if `T`'s `TypeKind` isn't a primitive.
    pub fn set_primitive_default_type<'a, T: Bauble<'a, A>, A: BaubleAllocator<'a>>(
        &mut self,
    ) -> &mut Self {
        let id = self.registry.get_or_register_type::<T, A>();

        self.registry.set_primitive_default_type(id);

        self
    }

    /// # Panics
    ///
    /// Panics if `TypeRegistry::validate(false)` returns false.
    pub fn build(self) -> BaubleContext {
        if let Err(e) = self.registry.validate(false) {
            panic!("Type system error: {e}");
        }
        let mut root_node = CtxNode::new(TypePath::empty());
        for (id, path) in self.default_uses.0 {
            root_node.add_node(id.borrow()).reference.redirect = Some(path);
        }
        for id in self.registry.type_ids() {
            if self.registry.key_type(id).meta.path.is_writable() {
                root_node.build_type(id, &self.registry);
            }
        }

        BaubleContext {
            registry: self.registry,
            root_node,
            files: Vec::new(),

            retry_files: Vec::new(),
        }
    }
}

#[derive(Clone, Debug)]
struct CtxNode {
    reference: InnerReference,
    path: TypePath,
    /// `Some` when this node is the top level module of a file (currently inline modules don't
    /// exist but there is some allowance for them).
    ///
    /// Set in [`BaubleContext::register_file`].
    source: Option<FileId>,
    children: IndexMap<TypePathElem, CtxNode>,
}

impl CtxNode {
    fn new(path: TypePath) -> Self {
        Self {
            path,
            reference: Default::default(),
            source: Default::default(),
            children: Default::default(),
        }
    }

    fn reference(&self, root: &Self) -> PathReference {
        let mut this = PathReference {
            ty: self.reference.ty,
            asset: self.reference.asset.map(|ty| (ty, self.path.clone())),
            module: (!self.children.is_empty()).then(|| self.path.clone()),
        };

        if let Some(redirect) = self.reference.redirect.as_ref()
            && let Some(node) = root.node_at(redirect.borrow())
        {
            let mut reference = node.reference(root);
            reference.combine_override(this);
            this = reference;
        }

        this
    }

    /// Recursively iterate all children of this node with an optional max depth of `max_depth`.
    fn iter_all_children<'a>(
        &'a self,
        max_depth: Option<usize>,
    ) -> impl Iterator<Item = &'a Self> + Clone {
        // pre-order depth first traversal
        let mut stack: Vec<(usize, indexmap::map::Values<'a, TypePathElem, CtxNode>)> = Vec::new();
        stack.push((0, self.children.values()));
        std::iter::from_fn(move || {
            while let Some((depth, iter)) = stack.last_mut() {
                let Some(inner) = iter.next() else {
                    stack.pop();
                    continue;
                };

                if max_depth.is_none_or(|d| *depth < d) {
                    let new_depth = *depth + 1;
                    stack.push((new_depth, inner.children.values()));
                }

                return Some(inner);
            }

            None
        })
    }

    #[expect(dead_code)]
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

    /// Gets node found at the end of the walking the provided path from the current node.
    ///
    /// Returns `None` if no node exists at this path.
    fn node_at(&self, path: TypePath<&str>) -> Option<&Self> {
        if let Some((root, rest)) = path.split_start() {
            self.children.get(&root).and_then(|node| node.node_at(rest))
        // Path is empty, get current node.
        } else {
            Some(self)
        }
    }

    /// Tries to find node where `visit` returns `Some`.
    ///
    /// We start at the end of `path` and walk up to the current node. Stops when `Some` is
    /// returned by `visit`.
    ///
    /// Returns the path that we got `Some` from and `R`.
    ///
    /// Returns `None` if `path` doesn't exist or if all `visit`ed nodes produced `None`.
    fn walk_find<'a, R: 'a>(
        &'a self,
        path: TypePath<&str>,
        mut visit: impl FnMut(&'a CtxNode) -> Option<R>,
    ) -> Option<(TypePath, R)> {
        fn walk_find_inner<'a, R: 'a>(
            node: &'a CtxNode,
            path: TypePath<&str>,
            visit: &mut impl FnMut(&'a CtxNode) -> Option<R>,
        ) -> Result<Option<(TypePath, R)>, ()> {
            if let Some((root, rest)) = path.split_start() {
                let Some(child_node) = node.children.get(&root) else {
                    // Path doesn't exist
                    return Err(());
                };
                walk_find_inner(child_node, rest, visit).map(|maybe| match maybe {
                    Some((mut path, r)) => {
                        path.push_start(root.into());

                        Some((path, r))
                    }
                    None => visit(node).map(|r| (TypePath::empty(), r)),
                })
            } else {
                // Path is empty
                Ok(visit(node).map(|r| (TypePath::empty(), r)))
            }
        }

        walk_find_inner(self, path, &mut visit).ok().flatten()
    }

    fn node_at_mut(&mut self, path: TypePath<&str>) -> Option<&mut Self> {
        if let Some((root, rest)) = path.split_start() {
            self.children
                .get_mut(&root)
                .and_then(|node| node.node_at_mut(rest))
        } else {
            Some(self)
        }
    }

    fn is_empty(&self) -> bool {
        self.reference.ty.is_none()
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
    fn build_nodes(&mut self, child_path: TypePath<&str>) -> &mut CtxNode {
        let Some((child, rest)) = child_path.split_start() else {
            return self;
        };
        self.add_node(child).build_nodes(rest)
    }

    fn add_node(&mut self, child: TypePathElem<&str>) -> &mut Self {
        self.children
            .entry(child.to_owned())
            .or_insert_with(|| CtxNode::new(self.path.join(&child)))
    }

    /// # Panics
    /// * If `id` isn't from `type_registry`.
    /// * If there are multiple entries at the same path.
    fn build_type(&mut self, id: TypeId, type_registry: &TypeRegistry) {
        let ty = type_registry.key_type(id);

        let node = self.build_nodes(ty.meta.path.borrow());
        if let Some(ty) = node.reference.ty
            && ty != id
        {
            panic!("Multiple types with the same path");
        }
        node.reference.ty = Some(id);
    }

    fn build_asset(&mut self, path: TypePath<&str>, ty: TypeId) {
        let node = self.build_nodes(path);
        if node.reference.asset.is_some() {
            panic!("Multiple types with the same path");
        }
        node.reference.asset = Some(ty);
    }
}

/// The ID associated with a context registered file.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FileId(usize);

/// The root of Bauble parsing.
///
/// The Bauble context is used to track the various source files for parsing and maintains
/// the [`TypeRegistry`] that describes every type and trait registered to Bauble.
#[derive(Clone)]
pub struct BaubleContext {
    registry: TypeRegistry,
    root_node: CtxNode,
    files: Vec<(TypePath, Source)>,

    retry_files: Vec<FileId>,
}

impl From<TypeRegistry> for BaubleContext {
    fn from(registry: TypeRegistry) -> Self {
        BaubleContextBuilder {
            registry,
            default_uses: DefaultUses::default(),
        }
        .build()
    }
}

fn preprocess_path(path: TypePath<&str>) -> TypePath<&str> {
    if let Some((path, end)) = path.split_end()
        && end.as_str() == "mod"
    {
        path
    } else {
        path
    }
}

impl BaubleContext {
    /// `path` describes the bauble "module" that the file corresponds to. That is it say, what prefix path
    /// is necessary inside of bauble to reference the context of this file.
    /// `source` is the string of Bauble text to be parsed.
    pub fn register_file(&mut self, path: TypePath<&str>, source: impl Into<String>) -> FileId {
        let path = preprocess_path(path);
        let node = self.root_node.build_nodes(path);
        let id = FileId(self.files.len());
        node.source = Some(id);
        self.files
            .push((path.to_owned(), ariadne::Source::from(source.into())));

        id
    }

    /// Iterates all registered files.
    pub fn files(&self) -> impl Iterator<Item = (TypePath<&str>, &str)> {
        self.files.iter().map(|e| (e.0.borrow(), e.1.text()))
    }

    /// Registers an asset. This is done automatically for any objects in a file that gets registered.
    ///
    /// With this method you can expose assets that aren't in bauble.
    pub fn register_asset(&mut self, path: TypePath<&str>, ty: TypeId) {
        let ref_ty = self.registry.get_or_register_asset_ref(ty);
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
            .map(|(path, source)| {
                let processed_path = preprocess_path(path.borrow());
                let file_id = self
                    .root_node
                    .node_at(processed_path)
                    .and_then(|node| node.source);
                match file_id {
                    Some(id) => {
                        *self.file_mut(id).1 = Source::from(source.into());
                        id
                    }
                    None => self.register_file(path.borrow(), source),
                }
            })
            .collect::<Vec<_>>();

        self.reload_files(ids)
    }

    fn parse(&self, file_id: FileId) -> Result<crate::parse::ParseValues, BaubleErrors> {
        use chumsky::Parser;

        let parser = crate::parse::parser();
        let result = parser.parse(crate::parse::ParserSource { file_id, ctx: self });

        result.into_result().map_err(|errors| {
            BaubleErrors::from(
                errors
                    .into_iter()
                    .map(|e| e.into_owned())
                    .collect::<Vec<_>>(),
            )
        })
    }

    /// This clears asset references in any of the file modules.
    fn reload_files<I: IntoIterator<Item = FileId>>(
        &mut self,
        new_files: I,
    ) -> (Vec<crate::Object>, BaubleErrors) {
        let mut files = std::mem::take(&mut self.retry_files);
        files.extend(new_files);
        files.sort_unstable();
        files.dedup();

        // Clear any previous assets that were loaded by these files.
        for file in files.iter() {
            // Need a partial borrow here.
            let (path, _) = &self.files[file.0];
            if let Some(node) = self.root_node.node_at_mut(path.borrow()) {
                node.clear_child_assets();
            }
        }

        let mut file_values = Vec::with_capacity(files.len());

        let mut skip = Vec::new();
        // Parse values, and return any errors.
        let mut errors = BaubleErrors::empty();
        for file in files.iter() {
            let values = match self.parse(*file) {
                Ok(values) => values,
                Err(err) => {
                    skip.push(*file);
                    errors.extend(err);
                    continue;
                }
            };

            file_values.push(values);
        }

        let mut skip_iter = skip.iter().copied().peekable();
        let mut new_skip = Vec::new();

        let mut delayed = Vec::new();

        for (file, values) in files.iter().zip(file_values.iter()).filter(|(file, _)| {
            if skip_iter.peek() == Some(file) {
                skip_iter.next();
                false
            } else {
                true
            }
        }) {
            // Need a partial borrow here.
            let (path, _) = self.file(*file);
            let path = path.to_owned();
            match crate::value::register_assets(path.borrow(), self, [], values) {
                Ok(d) => {
                    delayed.extend(d);
                }
                Err(e) => {
                    // Skip files that errored on registering.
                    new_skip.push(*file);
                    errors.extend(BaubleErrors::from(e));
                }
            }
        }

        skip.extend(new_skip);
        // TODO: Less hacky way to get which files errored here?
        if let Err(e) = crate::value::resolve_delayed(delayed, self) {
            // We want to skip any files that had errors.
            for e in e {
                skip.push(e.span.file());
                if let crate::ConversionError::Cycle(v) = &e.value {
                    skip.extend(v.iter().map(|s| s.0.span.file()))
                }
                errors.push(e);
            }
        }

        skip.sort_unstable();
        skip.dedup();

        let mut objects = Vec::new();

        let mut skip_iter = skip.iter().copied().peekable();

        for (file, values) in files.iter().zip(file_values).filter(|(file, _)| {
            if skip_iter.peek() == Some(file) {
                skip_iter.next();
                false
            } else {
                true
            }
        }) {
            match crate::value::convert_values(*file, values, &crate::value::Symbols::new(&*self)) {
                Ok(o) => objects.extend(o),
                Err(e) => errors.extend(e),
            }
        }

        self.retry_files.extend(skip);

        (objects, errors)
    }

    #[allow(missing_docs)]
    pub fn type_registry(&self) -> &TypeRegistry {
        &self.registry
    }

    /// Takes a path in bauble, and if the path is valid, return meta information about the
    /// bauble item at the current path.
    pub fn get_ref(&self, path: TypePath<&str>) -> Option<PathReference> {
        self.root_node
            .node_at(path)
            .map(|node| node.reference(&self.root_node))
    }

    /// Takes a path to a module in bauble, and if the path is valid, return the meta information
    /// of all items inside of thatm module (not recursive).
    pub fn all_in(&self, path: TypePath<&str>) -> Option<Vec<(TypePathElem, PathReference)>> {
        self.root_node.node_at(path).map(|node| {
            node.children
                .iter()
                .map(|(key, child_node)| (key.to_owned(), child_node.reference(&self.root_node)))
                .collect()
        })
    }

    // TODO(@docs)
    #[allow(missing_docs)]
    pub fn ref_with_ident(
        &self,
        path: TypePath<&str>,
        ident: TypePathElem<&str>,
    ) -> Option<PathReference> {
        self.root_node.node_at(path).and_then(|node| {
            node.iter_all_children(None)
                .filter(|node| node.path.ends_with(*ident.borrow()))
                .map(|node| node.reference(&self.root_node))
                .reduce(|a, mut b| {
                    b.combine_override(a);
                    b
                })
        })
    }

    /// If there is any associated file for `path`, get the ID of that file.
    ///
    /// `path` doesn't need to be the path of a file, it can be the path of anything in a file.
    ///
    /// Note, if a file `a` exists and a file `a::b::c` exists, `a::b` will get the ID of the file
    /// at `a`.
    pub fn get_file_id(&self, path: TypePath<&str>) -> Option<FileId> {
        self.root_node
            .walk_find(path, |node| node.source)
            .map(|(_, s)| s)
    }

    /// Get the module path of `file`.
    pub fn get_file_path(&self, file: FileId) -> TypePath<&str> {
        match self.files.get(file.0) {
            Some(p) => p.0.borrow(),
            None => {
                panic!(
                    "`FileId({})` is invalid, was it registered in another context?",
                    file.0
                );
            }
        }
    }

    /// Get the source used for parsing of `file`.
    pub fn get_source(&self, file: FileId) -> &Source {
        &self.files.get(file.0).expect("FileId was invalid").1
    }

    /// Get all the assets starting from `path`, with an optional maximum depth of `max_depth`.
    pub fn assets(
        &self,
        path: TypePath<&str>,
        max_depth: Option<usize>,
    ) -> impl Iterator<Item = TypePath<&str>> {
        self.root_node
            .node_at(path)
            .map(|node| node.iter_all_children(max_depth))
            .into_iter()
            .flatten()
            .filter(|node| node.reference(&self.root_node).asset.is_some())
            .map(|node| node.path.borrow())
    }

    /// Get all the types starting from `path`, with an optional maximum depth of `max_depth`.
    pub fn types(
        &self,
        path: TypePath<&str>,
        max_depth: Option<usize>,
    ) -> impl Iterator<Item = TypePath<&str>> {
        self.root_node
            .node_at(path)
            .map(|node| node.iter_all_children(max_depth))
            .into_iter()
            .flatten()
            .filter(|node| node.reference(&self.root_node).ty.is_some())
            .map(|node| node.path.borrow())
    }

    /// Get all the modules starting from `path`, with an optional maximum depth of `max_depth`.
    pub fn modules(
        &self,
        path: TypePath<&str>,
        max_depth: Option<usize>,
    ) -> impl Iterator<Item = TypePath<&str>> {
        self.root_node
            .node_at(path)
            .map(|node| node.iter_all_children(max_depth))
            .into_iter()
            .flatten()
            .filter(|node| node.reference(&self.root_node).module.is_some())
            .map(|node| node.path.borrow())
    }

    /// Get all the references starting from `path` which belong to `kind`, with an optional maximum depth of `max_depth`.
    pub fn ref_kinds(
        &self,
        path: TypePath<&str>,
        kind: crate::value::RefKind,
        max_depth: Option<usize>,
    ) -> impl Iterator<Item = TypePath<&str>> + Clone {
        self.root_node
            .node_at(path)
            .map(|node| node.iter_all_children(max_depth))
            .into_iter()
            .flatten()
            .filter(move |node| {
                let r = node.reference(&self.root_node);
                match kind {
                    crate::value::RefKind::Module => r.module.is_some(),
                    crate::value::RefKind::Asset => r.asset.is_some(),
                    crate::value::RefKind::Type => r.ty.is_some(),
                    crate::value::RefKind::Any => true,
                }
            })
            .map(|node| node.path.borrow())
    }
}

pub struct BaubleContextCache<'a>(pub &'a BaubleContext);

impl ariadne::Cache<FileId> for BaubleContextCache<'_> {
    type Storage = String;

    fn fetch(
        &mut self,
        id: &FileId,
    ) -> Result<&ariadne::Source<Self::Storage>, impl std::fmt::Debug> {
        Ok::<_, ()>(self.0.get_source(*id))
    }

    fn display<'b>(&self, id: &'b FileId) -> Option<impl std::fmt::Display + 'b> {
        Some(Box::new(self.0.get_file_path(*id).to_string()))
    }
}
