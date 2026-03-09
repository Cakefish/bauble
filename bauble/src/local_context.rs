use crate::context::BaubleContext;
use crate::path::{TypePath, TypePathElem};
use crate::types::TypeId;
use indexmap::IndexMap;

/// Assets are only referencable from other assets in the same file.
pub(crate) struct LocalAsset {
    /// Type of a Ref to this asset.
    ty: TypeId,
    // TODO: might not be necessary?
    /// Full path to this asset.
    ///
    /// This is the path to reach this node from the root.
    path: TypePath,
}

pub(crate) struct LocalAssets {
    assets: IndexMap<TypePathElem, LocalAsset>,
}

/// Transient context that is built and used when loading a file.
///
/// Contains registery of local assets.
pub(crate) struct LocalContext<'a> {
    local: IndexMap<TypePath, LocalAssets>,
    ctx: &'a mut BaubleContext,
}

impl LocalContext<'_> {
    /// Returns ID of internal Ref type for `ty`.
    pub fn register_asset(&mut self, path: TypePath, ty: TypeId) -> TypeId {
        let ref_ty = self.ctx.register_asset_ref_ty(ty);
        let asset = LocalAsset { ty: ref_ty, path };
        let (file, ident) = asset
            .path
            .get_end()
            .expect("Register asset with empty path");
        let assets = &mut self
            .local
            .entry(file.to_owned())
            .or_insert_with(|| LocalAssets {
                assets: IndexMap::new(),
            })
            .assets;
        if assets.contains_key(ident.as_str()) {
            panic!("{} refers to an existing asset", asset.path);
        } else {
            assets.insert(ident.to_owned(), asset);
        }

        ref_ty
    }
}
