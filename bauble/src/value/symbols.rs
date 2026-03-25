use std::{borrow::Cow, collections::HashMap};

use crate::{
    BaubleContext, CustomError,
    context::PathReference,
    parse::{Path, PathEnd, PathTreeEnd, PathTreeNode},
    path::{TypePath, TypePathElem},
    spanned::{SpanExt, Spanned},
    types::{self, TypeId, TypeRegistry},
};

use super::early_context::CombinedPathReference;
use super::{ConversionError, EarlyContext, PathKind, RefError, RefKind, Result};

/// Indicates kind of item being resolved by [`Symbols::resolve_path`] or
/// [`EarlySymbols::resolve_path`].
#[derive(Clone, Copy)]
pub(crate) enum ResolveKind {
    Type,
    Asset,
}

impl From<ResolveKind> for RefKind {
    fn from(kind: ResolveKind) -> Self {
        match kind {
            ResolveKind::Type => RefKind::Type,
            ResolveKind::Asset => RefKind::Asset,
        }
    }
}

/// Representation of item names available in the current module.
///
/// There are multiple namespaces: types, assets (i.e. values defined in bauble), and modules.
#[derive(Clone)]
pub(crate) struct Symbols<'a> {
    /// Context for looking up things referenced by full path.
    pub(super) ctx: &'a BaubleContext,
    /// Map of identifiers to path references.
    pub(super) uses: HashMap<TypePathElem, PathReference>,
}

impl<'a> Symbols<'a> {
    pub fn new(ctx: &'a BaubleContext) -> Self {
        Self {
            ctx,
            uses: HashMap::default(),
        }
    }

    pub fn add_ref(
        &mut self,
        ident: TypePathElem,
        reference: PathReference,
    ) -> std::result::Result<(), ConversionError> {
        let r = self.uses.entry(ident.clone()).or_default();

        *r = r
            .clone()
            .combined(reference)
            .ok_or(ConversionError::AmbiguousUse { ident })?;

        Ok(())
    }

    pub fn add_use(&mut self, use_path: &Spanned<PathTreeNode>) -> Result<()> {
        fn add_use_inner(
            this: &mut Symbols,
            leading: TypePath,
            end: &Spanned<PathTreeEnd>,
        ) -> Result<()> {
            match &end.value {
                PathTreeEnd::Group(g) => {
                    for node in g {
                        let mut leading = leading.clone();
                        for s in &node.leading.value {
                            leading.push_str(&s.value).map_err(|e| e.spanned(s.span))?;
                            if this.ctx.get_ref(leading.borrow()).is_none() {
                                return Err(ConversionError::RefError(Box::new(RefError {
                                    uses: None,
                                    path: PathKind::Direct(leading),
                                    path_ref: PathReference::empty().into(),
                                    kind: RefKind::Module,
                                }))
                                .spanned(s.span));
                            }
                        }
                        add_use_inner(this, leading, &node.end)?;
                    }
                }
                PathTreeEnd::Everything => {
                    if let Some(uses) = this.ctx.all_in(leading.borrow()) {
                        for (ident, reference) in uses {
                            this.add_ref(ident, reference)
                                .map_err(|e| e.spanned(end.span))?;
                        }
                    } else {
                        return Err(ConversionError::RefError(Box::new(RefError {
                            uses: None,
                            path: PathKind::Direct(leading),
                            path_ref: PathReference::empty().into(),
                            kind: RefKind::Module,
                        }))
                        .spanned(end.span));
                    }
                }
                PathTreeEnd::PathEnd(PathEnd::Ident(ident)) => {
                    let path_end =
                        TypePathElem::new(ident.as_str()).map_err(|e| e.spanned(ident.span))?;
                    let path = leading.join(&path_end);
                    if let Some(reference) = this.ctx.get_ref(path.borrow()) {
                        this.add_ref(path_end.to_owned(), reference)
                            .map_err(|e| e.spanned(ident.span))?;
                    } else {
                        return Err(ConversionError::RefError(Box::new(RefError {
                            uses: None,
                            path: PathKind::Direct(path),
                            path_ref: PathReference::empty().into(),
                            kind: RefKind::Any,
                        }))
                        .spanned(end.span));
                    }
                }
                PathTreeEnd::PathEnd(PathEnd::WithIdent(ident)) => {
                    let path_end =
                        TypePathElem::new(ident.as_str()).map_err(|e| e.spanned(ident.span))?;
                    if let Some(reference) = this.ctx.ref_with_ident(leading.borrow(), path_end) {
                        this.add_ref(path_end.to_owned(), reference)
                            .map_err(|e| e.spanned(ident.span))?;
                    } else {
                        return Err(ConversionError::RefError(Box::new(RefError {
                            uses: None,
                            path: PathKind::Indirect(leading, path_end.to_owned()),
                            path_ref: PathReference::empty().into(),
                            kind: RefKind::Any,
                        }))
                        .spanned(end.span));
                    }
                }
                PathTreeEnd::PathEnd(PathEnd::IdentGeneric(ident, ..))
                | PathTreeEnd::PathEnd(PathEnd::WithIdentGeneric(ident, ..)) => {
                    return Err(ConversionError::Custom(CustomError::new(
                        "Use cannot use generics",
                    ))
                    .spanned(ident.span));
                }
            }
            Ok(())
        }

        let mut leading = TypePath::empty();
        for l in use_path.leading.iter() {
            leading.push_str(l).map_err(|e| e.spanned(l.span))?;
            if self.ctx.get_ref(leading.borrow()).is_none() {
                return Err(ConversionError::RefError(Box::new(RefError {
                    uses: None,
                    path: PathKind::Direct(leading),
                    path_ref: PathReference::empty().into(),
                    kind: RefKind::Module,
                }))
                .spanned(l.span));
            }
        }
        add_use_inner(self, leading, &use_path.end)
    }

    fn get_module(&self, ident: &str) -> Option<TypePath> {
        self.uses
            .get(ident)
            .and_then(|reference| reference.module.clone())
    }

    fn resolve_path(&self, raw_path: &Path, kind: ResolveKind) -> Result<Spanned<PathKind>> {
        let mut leading = TypePath::empty();

        let mut path_iter = raw_path.leading.iter();
        if let Some(first) = path_iter.next() {
            leading = self.get_module(first.as_str()).unwrap_or(
                TypePath::new(first.as_str())
                    .map_err(|e| e.spanned(first.span))?
                    .to_owned(),
            );

            if self.ctx.get_ref(leading.borrow()).is_none() {
                return Err(ConversionError::RefError(Box::new(RefError {
                    uses: None,
                    path: PathKind::Direct(leading),
                    path_ref: PathReference::empty().into(),
                    kind: RefKind::Module,
                }))
                .spanned(first.span));
            }

            for ident in path_iter {
                leading
                    .push_str(ident.as_str())
                    .map_err(|e| e.spanned(ident.span))?;

                if self.ctx.get_ref(leading.borrow()).is_none() {
                    return Err(ConversionError::RefError(Box::new(RefError {
                        uses: None,
                        path: PathKind::Direct(leading),
                        path_ref: PathReference::empty().into(),
                        kind: RefKind::Module,
                    }))
                    .spanned(ident.span));
                }
            }
        }

        let generic_with_non_type_error = || {
            ConversionError::Custom(CustomError::new("Cannot use generics for non-type paths"))
                .spanned(raw_path.span())
        };
        let path = match &raw_path.last.value {
            PathEnd::WithIdent(ident) => PathKind::Indirect(
                leading,
                TypePathElem::new(ident.to_string()).map_err(|p| p.spanned(raw_path.span()))?,
            ),
            PathEnd::Ident(ident) => {
                let used = if leading.is_empty() {
                    self.uses.get(ident.as_str())
                } else {
                    None
                };
                let path = if let Some(r) = used
                    && let ResolveKind::Type = kind
                    && let Some(ty) = r.ty
                {
                    self.ctx.type_registry().key_type(ty).meta.path.clone()
                } else if let Some(r) = used
                    && let ResolveKind::Asset = kind
                    && let Some((_ty, path, _kind)) = &r.asset
                {
                    path.clone()
                } else {
                    leading
                        .push_str(ident.as_str())
                        .map_err(|p| p.spanned(raw_path.span()))?;
                    leading
                };
                PathKind::Direct(path)
            }
            PathEnd::WithIdentGeneric(ident, generic) => {
                if !matches!(kind, ResolveKind::Type) {
                    return Err(generic_with_non_type_error());
                }
                let generic = self.resolve_path(&generic.value, ResolveKind::Type)?;
                PathKind::Indirect(
                    leading,
                    TypePathElem::new(format!("{ident}<{generic}>"))
                        .map_err(|p| p.spanned(raw_path.span()))?,
                )
            }
            PathEnd::IdentGeneric(ident, generic) => {
                if !matches!(kind, ResolveKind::Type) {
                    return Err(generic_with_non_type_error());
                }
                let generic = self.resolve_path(&generic.value, ResolveKind::Type)?;
                let path = if leading.is_empty()
                    && let Some(r) = self.uses.get(ident.as_str())
                    && let Some(ty) = r.ty
                {
                    let outer_path = &self.ctx.type_registry().key_type(ty).meta.path;
                    TypePath::new(format!("{outer_path}<{generic}>"))
                        .map_err(|p| p.spanned(raw_path.span()))?
                } else {
                    leading
                        .push_str(&format!("{ident}<{generic}>"))
                        .map_err(|p| p.spanned(raw_path.span()))?;
                    leading
                };
                PathKind::Direct(path)
            }
        };
        Ok(path.spanned(raw_path.span()))
    }

    /// Note, the returned `PathReference` only makes sense to use for the `kind` passed here. The
    /// same path for a different `kind` may return a different `PathReference`.
    fn resolve_item(&self, raw_path: &Path, kind: ResolveKind) -> Result<Cow<'_, PathReference>> {
        // NOTE: This resolves the full path referred to via `uses`. This is unnecessary in many
        // cases because there is a `PathReference` is available in `self.uses`.
        //
        // However, there would be a few complications:
        // 1. Paths for generic types always need to be fully resolved.
        // 2. If a particular identifier is available at the root of the `BaubleContext` in one
        //    namespace (e.g. type namespace) and in `self.uses` in another namespace (e.g. asset
        //    namespace) then we could miss something if we naively return the `PathReference` from
        //    `self.uses` (we would need to at least check `BaubleContext` if the `kind` of item
        //    was `None` in `self.uses`).
        let path = self.resolve_path(raw_path, kind)?;

        let reference = match &path.value {
            PathKind::Direct(path) => self.ctx.get_ref(path.borrow()).map(Cow::Owned),
            PathKind::Indirect(path, ident) => self
                .ctx
                .ref_with_ident(path.borrow(), ident.borrow())
                .map(Cow::Owned),
        };

        reference.ok_or_else(|| {
            if let PathKind::Direct(path) = &*path
                && let Some((leading, ident)) = path.get_end()
                && let Some(r) = self.ctx.get_ref(leading)
                && let Some(ty) = r.ty
                && matches!(
                    self.ctx.type_registry().key_type(ty).kind,
                    types::TypeKind::Enum { .. } | types::TypeKind::Or(_)
                )
            {
                ConversionError::UnknownVariant {
                    variant: ident.to_owned().spanned(raw_path.last.span),
                    ty,
                }
            } else {
                ConversionError::RefError(Box::new(RefError {
                    uses: Some(self.uses.keys().cloned().collect()),
                    path: path.value.clone(),
                    path_ref: PathReference::empty().into(),
                    kind: kind.into(),
                }))
            }
            .spanned(raw_path.span())
        })
    }

    pub fn resolve_asset(&self, path: &Path) -> Result<(TypeId, TypePath)> {
        let item = self.resolve_item(path, ResolveKind::Asset)?.into_owned();

        if let Some((ty, path, _kind)) = item.asset {
            Ok((ty, path))
        } else {
            Err(ConversionError::RefError(Box::new(RefError {
                uses: Some(self.uses.keys().cloned().collect()),
                path: self.resolve_path(path, ResolveKind::Asset)?.value,
                path_ref: item.into(),
                kind: RefKind::Asset,
            }))
            .spanned(path.span()))
        }
    }

    pub fn resolve_type(&self, path: &Path) -> Result<TypeId> {
        let item = self.resolve_item(path, ResolveKind::Type)?;

        if let Some(ty) = item.ty {
            Ok(ty)
        } else {
            Err(ConversionError::RefError(Box::new(RefError {
                uses: Some(self.uses.keys().cloned().collect()),
                path: self.resolve_path(path, ResolveKind::Type)?.value,
                path_ref: item.into_owned().into(),
                kind: RefKind::Type,
            }))
            .spanned(path.span()))
        }
    }
}

/// Representation of item names available in the current module.
///
/// This is used before types of assets are fully resolved. Afterwards, [`Symbols`] can be used.
///
/// There are multiple namespaces: types, assets (i.e. values defined in bauble), and modules.
pub(crate) struct EarlySymbols<'a, 'b> {
    /// Context for looking up things referenced by full path.
    ///
    /// This does not need mutable access but the user of `EarlySymbols` needs to mutate
    /// `BaubleContext`, so it is convenient to hold a mutable reference here.
    pub(super) ctx: &'a mut EarlyContext<'b>,
    /// Map of identifiers to path references.
    pub(super) uses: HashMap<TypePathElem, CombinedPathReference>,
}

impl<'a, 'b> EarlySymbols<'a, 'b> {
    pub fn new(ctx: &'a mut EarlyContext<'b>) -> Self {
        Self {
            ctx,
            uses: HashMap::default(),
        }
    }

    pub fn bauble_ctx(&mut self) -> &mut BaubleContext {
        self.ctx.ctx
    }

    pub fn add_ref(
        &mut self,
        ident: TypePathElem,
        reference: CombinedPathReference,
    ) -> std::result::Result<(), ConversionError> {
        let r = self.uses.entry(ident.clone()).or_default();

        *r = r
            .clone()
            .combined(reference)
            .ok_or(ConversionError::AmbiguousUse { ident })?;

        Ok(())
    }

    pub fn add_use(&mut self, use_path: &Spanned<PathTreeNode>) -> Result<()> {
        fn add_use_inner(
            this: &mut EarlySymbols,
            leading: TypePath,
            end: &Spanned<PathTreeEnd>,
        ) -> Result<()> {
            match &end.value {
                PathTreeEnd::Group(g) => {
                    for node in g {
                        let mut leading = leading.clone();
                        for s in &node.leading.value {
                            leading.push_str(&s.value).map_err(|e| e.spanned(s.span))?;
                            if this.ctx.get_ref(leading.borrow()).is_none() {
                                return Err(ConversionError::RefError(Box::new(RefError {
                                    uses: None,
                                    path: PathKind::Direct(leading),
                                    path_ref: PathReference::empty().into(),
                                    kind: RefKind::Module,
                                }))
                                .spanned(s.span));
                            }
                        }
                        add_use_inner(this, leading, &node.end)?;
                    }
                }
                PathTreeEnd::Everything => {
                    if let Some(uses) = this.ctx.all_in(leading.borrow()) {
                        for (ident, reference) in uses {
                            this.add_ref(ident, reference)
                                .map_err(|e| e.spanned(end.span))?;
                        }
                    } else {
                        return Err(ConversionError::RefError(Box::new(RefError {
                            uses: None,
                            path: PathKind::Direct(leading),
                            path_ref: PathReference::empty().into(),
                            kind: RefKind::Module,
                        }))
                        .spanned(end.span));
                    }
                }
                PathTreeEnd::PathEnd(PathEnd::Ident(ident)) => {
                    let path_end =
                        TypePathElem::new(ident.as_str()).map_err(|e| e.spanned(ident.span))?;
                    let path = leading.join(&path_end);
                    if let Some(reference) = this.ctx.get_ref(path.borrow()) {
                        this.add_ref(path_end.to_owned(), reference)
                            .map_err(|e| e.spanned(ident.span))?;
                    } else {
                        return Err(ConversionError::RefError(Box::new(RefError {
                            uses: None,
                            path: PathKind::Direct(path),
                            path_ref: PathReference::empty().into(),
                            kind: RefKind::Any,
                        }))
                        .spanned(end.span));
                    }
                }
                PathTreeEnd::PathEnd(PathEnd::WithIdent(ident)) => {
                    let path_end =
                        TypePathElem::new(ident.as_str()).map_err(|e| e.spanned(ident.span))?;
                    if let Some(reference) = this.ctx.ref_with_ident(leading.borrow(), path_end) {
                        this.add_ref(path_end.to_owned(), reference)
                            .map_err(|e| e.spanned(ident.span))?;
                    } else {
                        return Err(ConversionError::RefError(Box::new(RefError {
                            uses: None,
                            path: PathKind::Indirect(leading, path_end.to_owned()),
                            path_ref: PathReference::empty().into(),
                            kind: RefKind::Any,
                        }))
                        .spanned(end.span));
                    }
                }
                PathTreeEnd::PathEnd(PathEnd::IdentGeneric(ident, ..))
                | PathTreeEnd::PathEnd(PathEnd::WithIdentGeneric(ident, ..)) => {
                    return Err(ConversionError::Custom(CustomError::new(
                        "Use cannot use generics",
                    ))
                    .spanned(ident.span));
                }
            }
            Ok(())
        }

        let mut leading = TypePath::empty();
        for l in use_path.leading.iter() {
            leading.push_str(l).map_err(|e| e.spanned(l.span))?;
            if self.ctx.get_ref(leading.borrow()).is_none() {
                return Err(ConversionError::RefError(Box::new(RefError {
                    uses: None,
                    path: PathKind::Direct(leading),
                    path_ref: PathReference::empty().into(),
                    kind: RefKind::Module,
                }))
                .spanned(l.span));
            }
        }
        add_use_inner(self, leading, &use_path.end)
    }

    fn get_module(&self, ident: &str) -> Option<TypePath> {
        self.uses
            .get(ident)
            .and_then(|reference| reference.module.clone())
    }

    pub fn resolve_path(&self, raw_path: &Path, kind: ResolveKind) -> Result<Spanned<PathKind>> {
        let mut leading = TypePath::empty();

        let mut path_iter = raw_path.leading.iter();
        if let Some(first) = path_iter.next() {
            leading = self.get_module(first.as_str()).unwrap_or(
                TypePath::new(first.as_str())
                    .map_err(|e| e.spanned(first.span))?
                    .to_owned(),
            );

            if self.ctx.get_ref(leading.borrow()).is_none() {
                return Err(ConversionError::RefError(Box::new(RefError {
                    uses: None,
                    path: PathKind::Direct(leading),
                    path_ref: PathReference::empty().into(),
                    kind: RefKind::Module,
                }))
                .spanned(first.span));
            }

            for ident in path_iter {
                leading
                    .push_str(ident.as_str())
                    .map_err(|e| e.spanned(ident.span))?;

                if self.ctx.get_ref(leading.borrow()).is_none() {
                    return Err(ConversionError::RefError(Box::new(RefError {
                        uses: None,
                        path: PathKind::Direct(leading),
                        path_ref: PathReference::empty().into(),
                        kind: RefKind::Module,
                    }))
                    .spanned(ident.span));
                }
            }
        }

        let generic_with_non_type_error = || {
            ConversionError::Custom(CustomError::new("Cannot use generics for non-type paths"))
                .spanned(raw_path.span())
        };
        let path = match &raw_path.last.value {
            PathEnd::WithIdent(ident) => PathKind::Indirect(
                leading,
                TypePathElem::new(ident.to_string()).map_err(|p| p.spanned(raw_path.span()))?,
            ),
            PathEnd::Ident(ident) => {
                let used = if leading.is_empty() {
                    self.uses.get(ident.as_str())
                } else {
                    None
                };
                let path = if let Some(r) = used
                    && let ResolveKind::Type = kind
                    && let Some(ty) = r.ty
                {
                    self.ctx.type_registry().key_type(ty).meta.path.clone()
                } else if let Some(r) = used
                    && let ResolveKind::Asset = kind
                    && let Some((_ty, path, _kind)) = &r.asset
                {
                    path.clone()
                } else {
                    leading
                        .push_str(ident.as_str())
                        .map_err(|p| p.spanned(raw_path.span()))?;
                    leading
                };
                PathKind::Direct(path)
            }
            PathEnd::WithIdentGeneric(ident, generic) => {
                if !matches!(kind, ResolveKind::Type) {
                    return Err(generic_with_non_type_error());
                }
                let generic = self.resolve_path(&generic.value, ResolveKind::Type)?;
                PathKind::Indirect(
                    leading,
                    TypePathElem::new(format!("{ident}<{generic}>"))
                        .map_err(|p| p.spanned(raw_path.span()))?,
                )
            }
            PathEnd::IdentGeneric(ident, generic) => {
                if !matches!(kind, ResolveKind::Type) {
                    return Err(generic_with_non_type_error());
                }
                let generic = self.resolve_path(&generic.value, ResolveKind::Type)?;
                let path = if leading.is_empty()
                    && let Some(r) = self.uses.get(ident.as_str())
                    && let Some(ty) = r.ty
                {
                    let outer_path = &self.ctx.type_registry().key_type(ty).meta.path;
                    TypePath::new(format!("{outer_path}<{generic}>"))
                        .map_err(|p| p.spanned(raw_path.span()))?
                } else {
                    leading
                        .push_str(&format!("{ident}<{generic}>"))
                        .map_err(|p| p.spanned(raw_path.span()))?;
                    leading
                };
                PathKind::Direct(path)
            }
        };
        Ok(path.spanned(raw_path.span()))
    }

    /// Note, the returned `PathReference` only makes sense to use for the `kind` passed here. The
    /// same path for a different `kind` may return a different `PathReference`.
    fn resolve_item(
        &self,
        raw_path: &Path,
        kind: ResolveKind,
    ) -> Result<Cow<'_, CombinedPathReference>> {
        // NOTE: Similar to `Symbols::resolve_item`, this resolves the full path referred which is
        // often unneccessary.
        //
        // But avoiding this has the same complications along with an additional ones:
        // 3. There are other uses of `resolve_path` that need a full path because the resolved
        //    path needs to be looked up later when `EarlySymbols` is no longer available.
        // 4. Once an asset is registered with its type, the path reference stored in `uses` will
        //    be outdated since it won't include the type (an up-to-date value isn't essential but
        //    would lead to fewer assets to process in resolve_delayed).
        let path = self.resolve_path(raw_path, kind)?;

        let reference = match &path.value {
            PathKind::Direct(path) => self.ctx.get_ref(path.borrow()).map(Cow::Owned),
            PathKind::Indirect(path, ident) => self
                .ctx
                .ref_with_ident(path.borrow(), ident.borrow())
                .map(Cow::Owned),
        };

        reference.ok_or_else(|| {
            if let PathKind::Direct(path) = &*path
                && let Some((leading, ident)) = path.get_end()
                && let Some(r) = self.ctx.get_ref(leading)
                && let Some(ty) = r.ty
                && matches!(
                    self.ctx.type_registry().key_type(ty).kind,
                    types::TypeKind::Enum { .. } | types::TypeKind::Or(_)
                )
            {
                ConversionError::UnknownVariant {
                    variant: ident.to_owned().spanned(raw_path.last.span),
                    ty,
                }
            } else {
                ConversionError::RefError(Box::new(RefError {
                    uses: Some(self.uses.keys().cloned().collect()),
                    path: path.value.clone(),
                    path_ref: PathReference::empty().into(),
                    kind: kind.into(),
                }))
            }
            .spanned(raw_path.span())
        })
    }

    pub fn resolve_type(&self, path: &Path) -> Result<TypeId> {
        let item = self.resolve_item(path, ResolveKind::Type)?;

        if let Some(ty) = item.ty {
            Ok(ty)
        } else {
            Err(ConversionError::RefError(Box::new(RefError {
                uses: Some(self.uses.keys().cloned().collect()),
                path: self.resolve_path(path, ResolveKind::Type)?.value,
                path_ref: item.into_owned(),
                kind: RefKind::Type,
            }))
            .spanned(path.span()))
        }
    }
}

pub(crate) trait SymbolsCommon {
    fn resolve_asset_type(&self, path: &Path) -> Result<Option<TypeId>>;
    fn resolve_type(&self, path: &Path) -> Result<TypeId>;
    fn type_registry(&self) -> &TypeRegistry;
}

impl SymbolsCommon for Symbols<'_> {
    fn resolve_asset_type(&self, path: &Path) -> Result<Option<TypeId>> {
        self.resolve_asset(path).map(|(ty, _)| Some(ty))
    }

    fn resolve_type(&self, path: &Path) -> Result<TypeId> {
        self.resolve_type(path)
    }

    fn type_registry(&self) -> &TypeRegistry {
        self.ctx.type_registry()
    }
}

impl SymbolsCommon for EarlySymbols<'_, '_> {
    /// Note, if an asset isn't registered in `BaubleContext` yet, its type will be unknown.
    fn resolve_asset_type(&self, path: &Path) -> Result<Option<TypeId>> {
        let item = self.resolve_item(path, ResolveKind::Asset)?.into_owned();

        if let Some((ty, _path, _kind)) = item.asset {
            Ok(ty)
        } else {
            Err(ConversionError::RefError(Box::new(RefError {
                uses: Some(self.uses.keys().cloned().collect()),
                path: self.resolve_path(path, ResolveKind::Asset)?.value,
                path_ref: item,
                kind: RefKind::Asset,
            }))
            .spanned(path.span()))
        }
    }

    fn resolve_type(&self, path: &Path) -> Result<TypeId> {
        self.resolve_type(path)
    }

    fn type_registry(&self) -> &TypeRegistry {
        self.ctx.type_registry()
    }
}
