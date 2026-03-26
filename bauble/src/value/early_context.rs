use crate::context::{AssetKind, BaubleContext, PathReference};
use crate::path::{TypePath, TypePathElem};
use crate::types::TypeId;
use crate::value::AmbiguousWithIdent;
use indexmap::IndexMap;

fn try_reduce_option<T>(
    a: Option<T>,
    b: Option<T>,
    f: impl FnOnce(T, T) -> Result<T, ()>,
) -> Result<Option<T>, ()> {
    match (a, b) {
        (Some(a), Some(b)) => f(a, b).map(Some),
        (Some(t), None) | (None, Some(t)) => Ok(Some(t)),
        (None, None) => Ok(None),
    }
}

/// - Returns `None` if both are `Some`.
/// - Returns `Some(None)` if both are `None`.
/// - Returns `Some(Some(_))` when only one of the provided options is `Some`.
fn xor_option<T>(a: Option<T>, b: Option<T>) -> Option<Option<T>> {
    try_reduce_option(a, b, |_, _| Err(())).ok()
}

/// A type containing multiple references generally derived from a path.
///
/// Generalization of both [`PathReference`] and [`EarlyPathReference`].
///
/// Unlike [`PathReference`] the type for an asset may not yet be known.
#[derive(Default, Clone, Debug)]
pub(crate) struct CombinedPathReference {
    /// The type referenced by a path.
    pub ty: Option<TypeId>,
    /// The asset (and its path) referenced by the path.
    pub asset: Option<(Option<TypeId>, TypePath, AssetKind)>,
    /// If the reference references a module.
    pub module: Option<TypePath>,
}

impl CombinedPathReference {
    /// Combines an [`EarlyPathReference`] into this.
    ///
    /// Like [`combined`](Self::combined), except:
    /// 1. This mutates `self` in-place.
    /// 2. `Some` is allowed in matching fields if the contents are the same.
    ///
    /// This is used to combine the [`EarlyPathReference`] obtained from pre-registered assets with
    /// the [`PathReference`] for existing items in [`BaubleContext`]. During the type resolution
    /// process assets/modules will exist in both places as they are registered into
    /// [`BaubleContext`].
    ///
    /// Returns an error if there is a collision where matching fields both have `Some(_)` but they
    /// are for different items so their contents don't match.
    fn combine_early(&mut self, other: EarlyPathReference) -> Result<(), ()> {
        let EarlyPathReference {
            asset: other_asset,
            module: other_module,
        } = other;

        if let (Some((other_path, other_kind)), Some((_this_ty, this_path, this_kind))) =
            (&other_asset, &self.asset)
            && (this_path, this_kind) != (other_path, other_kind)
        {
            return Err(());
        }
        if let (Some(other_module), Some(module)) = (&other_module, &self.module)
            && module != other_module
        {
            return Err(());
        }
        // Only mutate after checking that no conflicts exist.
        if self.asset.is_none() {
            self.asset = other_asset.map(|(other_path, other_kind)| (None, other_path, other_kind));
        }
        if self.module.is_none() {
            self.module = other_module;
        }

        Ok(())
    }

    /// Take the exclusive properties of `self` and `other`, essentially "xor"ing them together by producing
    /// the combined result where each field where both are `Some` are `None`.
    ///
    /// Returns `None` if there is a collision (i.e. matching fields are `Some`).
    pub(super) fn combined(self, other: Self) -> Option<Self> {
        Some(Self {
            ty: xor_option(self.ty, other.ty)?,
            asset: xor_option(self.asset, other.asset)?,
            module: xor_option(self.module, other.module)?,
        })
    }
}

/// A type containing multiple references generally derived from a path.
///
/// Unlike [`PathReference`] the type for an asset is not known. Also this doesn't include
/// information about a potential type referenced by this path.
///
/// This can be combined into a [`CombinedPathReference`] which can be constructed from a standard
/// [`PathReference`].
#[derive(Default, Clone, Debug)]
struct EarlyPathReference {
    /// The asset (and its path) referenced by the path.
    pub asset: Option<(TypePath, AssetKind)>,
    /// If the reference references a module.
    pub module: Option<TypePath>,
}

impl EarlyPathReference {
    /// Combine references of `self` with references of `other`.
    ///
    /// If there is a collision, `self` will be unchanged and this returns `false`.
    fn combine(&mut self, other: Self) -> bool {
        if self.asset.is_some() && other.asset.is_some()
            || self.module.is_some() && other.module.is_some()
        {
            false
        } else {
            if other.asset.is_some() {
                self.asset = other.asset;
            }
            if other.module.is_some() {
                self.module = other.module;
            }
            true
        }
    }
}

impl From<EarlyPathReference> for CombinedPathReference {
    fn from(reference: EarlyPathReference) -> Self {
        Self {
            ty: None,
            asset: reference.asset.map(|(path, kind)| (None, path, kind)),
            module: reference.module,
        }
    }
}

impl From<PathReference> for CombinedPathReference {
    fn from(reference: PathReference) -> Self {
        Self {
            ty: reference.ty,
            asset: reference
                .asset
                .map(|(ty, path, kind)| (Some(ty), path, kind)),
            module: reference.module,
        }
    }
}

/// Represents a name in one or multiple of the asset and module namespaces.
///
/// If there is a module at this name, this holds a list of the `CtxNode`s in that module.
#[derive(Clone, Debug)]
struct CtxNode {
    /// Full path to this node.
    ///
    /// This is the path to reach this node from the root.
    path: TypePath,
    /// This name can potentially reference:
    /// * An asset
    /// * A module (not represented here but via the `Self::children` field).
    // TODO: stage 2: only hold top level assets here, local assets should not need to exist here
    asset: Option<AssetKind>,
    children: IndexMap<TypePathElem, CtxNode>,
}

impl CtxNode {
    fn new(path: TypePath) -> Self {
        Self {
            path,
            asset: None,
            children: IndexMap::<_, _>::default(),
        }
    }

    fn reference(&self) -> EarlyPathReference {
        EarlyPathReference {
            asset: self.asset.map(|kind| (self.path.clone(), kind)),
            module: (!self.children.is_empty()).then(|| self.path.clone()),
        }
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

    fn build_asset(&mut self, path: TypePath<&str>, kind: AssetKind) -> Result<(), ()> {
        let node = self.build_nodes(path);
        if node.asset.is_some() {
            // Multiple assets with the same path
            return Err(());
        }

        node.asset = Some(kind);
        Ok(())
    }
}

/// New assets that are known to exist but have not had their types resolved and aren't registered
/// in `BaubleContext`.
///
/// Structured as a node tree because we need to be able to iterate items in a particular module.
pub(crate) struct EarlyContext<'a> {
    /// Already registered types, assets, and modules. Used to look these up to check for conflicts
    /// and combine with the pending assets when querying for items.
    ///
    /// This does not need mutable access but the consumer of `EarlyContext` needs to mutate
    /// `BaubleContext`.
    pub(crate) ctx: &'a mut BaubleContext,
    /// Pending assets and modules that have not fully loaded yet. At this point their types are
    /// unknown. When their types are resolved they will be registered into `BaubleContext`.
    root_node: CtxNode,
}

impl<'a> EarlyContext<'a> {
    pub fn new(ctx: &'a mut BaubleContext) -> Self {
        let root_node = CtxNode::new(TypePath::empty());
        Self { ctx, root_node }
    }

    /// Registers an asset. This is done automatically for any objects in a file that gets registered.
    ///
    /// With this method you can expose assets that aren't in bauble.
    ///
    /// Returns ID of internal Ref type for `ty`.
    ///
    /// Returns an error if an asset was already registered at this path. This can occur due to
    /// simplification of the top level asset path to match the current file. E.g. the top-level
    /// asset in `a::1` will conflict with the path of object `1` in file `a`.
    //
    // TODO: in stage 2 we might be able to adjust this so that local object paths are
    // distinguished from top level objects, such that they don't clash.
    pub fn register_asset(
        &mut self,
        path: TypePath<&str>,
        kind: AssetKind,
    ) -> Result<(), crate::CustomError> {
        // Make sure asset doesn't already exist in `BaubleContext`.
        if self.ctx.get_ref(path).is_some_and(|r| r.asset.is_some()) {
            // TODO: this error should no longer be possible?
            return Err(crate::CustomError::new(format!(
                "'{path}' refers to an existing asset in another file. This can be \n\
                caused by special cased path simplification for the first object in a \n\
                file.",
            )));
        }

        self.root_node
            .build_asset(path, kind)
            // TODO: this error should no longer be possible?
            .map_err(|()| {
                crate::CustomError::new(format!(
                    "'{path}' refers to an existing asset in another file. This can be \n\
                caused by special cased path simplification for the first object in a \n\
                file.",
                ))
            })
    }

    /// Takes a path in bauble, and if the path is valid, return meta information about the
    /// bauble item(s) at that path.
    ///
    /// Looks up from both pending items and items already registered in [`BaubleContext`].
    pub fn get_ref(&self, path: TypePath<&str>) -> Option<CombinedPathReference> {
        let a = self.ctx.get_ref(path).map(CombinedPathReference::from);
        let b = self.root_node.node_at(path).map(|node| node.reference());

        if let Some(mut a) = a {
            if let Some(b) = b {
                a.combine_early(b).expect("Unexpected collision");
            }

            Some(a)
        } else {
            b.map(CombinedPathReference::from)
        }
    }

    /// Recursively searches all children of the node at `path` for node with path ending in
    /// `ident`.
    ///
    /// Returns the [`PathReference`] from [`CtxNode::reference`]. If multiple nodes are found with
    /// `ident`, they will be combined and this will return an error if they have items in the same
    /// namespace.
    ///
    /// Looks up from both pending items and items already registered in [`BaubleContext`].
    pub fn ref_with_ident(
        &self,
        path: TypePath<&str>,
        ident: TypePathElem<&str>,
    ) -> Result<Option<CombinedPathReference>, AmbiguousWithIdent> {
        let mut collided = false;
        let a = self
            .ctx
            .ref_with_ident(path, ident)?
            .map(CombinedPathReference::from);
        let b = self.root_node.node_at(path).and_then(|node| {
            node.iter_all_children(None)
                .filter(|node| node.path.ends_with(*ident.borrow()))
                .map(|node| node.reference())
                .reduce(|mut a, b| {
                    if !a.combine(b) {
                        collided = true;
                    }
                    a
                })
        });
        if collided {
            return Err(AmbiguousWithIdent {
                path: path.to_owned(),
                ident: ident.to_owned(),
            });
        }

        Ok(if let Some(mut a) = a {
            if let Some(b) = b {
                a.combine_early(b).map_err(|()| AmbiguousWithIdent {
                    path: path.to_owned(),
                    ident: ident.to_owned(),
                })?;
            }

            Some(a)
        } else {
            b.map(CombinedPathReference::from)
        })
    }

    /// Takes a path to a module in bauble, and if the path is valid, return the meta information
    /// of all items inside of that module (not recursive).
    ///
    /// Looks up from both pending items and items already registered in [`BaubleContext`].
    ///
    /// Note, the order of returned items won't match after these pending items are registered into
    /// [`BaubleContext`].
    pub fn all_in(
        &self,
        path: TypePath<&str>,
    ) -> Option<Vec<(TypePathElem, CombinedPathReference)>> {
        let maybe_items = self.ctx.all_in(path).map(|items| {
            items
                .into_iter()
                .map(|(ident, reference)| (ident, CombinedPathReference::from(reference)))
        });
        if let Some(node) = self.root_node.node_at(path) {
            let mut items = maybe_items
                .map(|items| items.collect::<IndexMap<_, _>>())
                .unwrap_or_default();
            node.children.iter().for_each(|(key, child_node)| {
                let key = key.to_owned();
                let r = child_node.reference();
                use indexmap::map::Entry;
                match items.entry(key) {
                    Entry::Occupied(mut e) => {
                        e.get_mut().combine_early(r).expect("Unexpected collision")
                    }
                    Entry::Vacant(e) => {
                        e.insert(CombinedPathReference::from(r));
                    }
                }
            });
            Some(items.into_iter().collect())
        } else {
            maybe_items.map(|items| items.collect())
        }
    }

    pub fn type_registry(&self) -> &crate::types::TypeRegistry {
        self.ctx.type_registry()
    }
}
