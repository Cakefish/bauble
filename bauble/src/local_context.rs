use crate::context::BaubleContext;
use crate::path::TypePath;
use crate::types::TypeId;
use indexmap::IndexMap;

/// Transient context that is built and used when loading file(s).
///
/// Contains registery of local objects. These are objects that are only referencable by other
/// objects in the same file.
pub(crate) struct LocalContext {
    /// Map of local object paths to type ID of a Ref type to each object.
    objects: IndexMap<TypePath, TypeId>,
}

impl LocalContext {
    /// Creates a new local context.
    pub fn new() -> Self {
        Self {
            objects: IndexMap::new(),
        }
    }

    /// Registers a local object.
    ///
    /// `BaubleContext` parameter is used to retrieve/register `Ref<T>` type for this object.
    ///
    /// # Panics
    /// Panics if an object was already registered at this path.
    pub fn register(&mut self, path: TypePath, ty: TypeId, ctx: &mut BaubleContext) {
        let ref_ty = ctx.register_asset_ref_ty(ty);
        if self.objects.contains_key(path.as_str()) {
            panic!("{} refers to an existing object", path);
        } else {
            self.objects.insert(path, ref_ty);
        }
    }

    /// Returns type of local bauble object at this path (if one exists).
    pub fn get(&self, path: TypePath<&str>) -> Option<TypeId> {
        self.objects.get(&path).copied()
    }
}
