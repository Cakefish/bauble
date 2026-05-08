use std::{borrow::Cow, collections::HashMap};

use crate::{
    BaubleContext, CustomError,
    context::PathReference,
    local_context::LocalContext,
    parse::{Path, PathEnd, PathTreeEnd, PathTreeNode},
    path::{TypePath, TypePathElem},
    spanned::{SpanExt, Spanned},
    types::{self, TypeId, TypeRegistry},
};

use super::early_context::CombinedPathReference;
use super::{
    ConversionError, EarlyContext, ObjectPath, PathKind, RefError, RefKind, Result,
    error::ErrorPathReference,
};

/// Indicates kind of item being resolved by [`Symbols::resolve_path`] or
/// [`EarlySymbols::resolve_path`].
#[derive(Clone, Copy)]
enum ResolveKind {
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

fn generic_with_non_type_error(raw_path: &Path) -> Spanned<ConversionError> {
    ConversionError::Custom(CustomError::new("Cannot use generics for non-type paths"))
        .spanned(raw_path.span())
}

fn generic_param_using_with_ident(span: crate::Span) -> Spanned<ConversionError> {
    ConversionError::Custom(CustomError::new(
        "Cannot use path::*::ident syntax in generic parameters",
    ))
    .spanned(span)
}

/// `PathReference` for `Symbols` `uses`. Distinguishes between local and top level objects.
#[derive(Default, Clone)]
struct UseReference {
    ty: Option<TypeId>,
    asset: Option<(TypeId, ObjectPath)>,
    module: Option<TypePath>,
}

impl UseReference {
    /// Take the exclusive properties of `self` and `other`, essentially "xor"ing them together by producing
    /// the combined result where each field where both are `Some` are `None`.
    pub fn combined(self, other: Self) -> Option<Self> {
        Some(Self {
            ty: xor_option(self.ty, other.ty)?,
            asset: xor_option(self.asset, other.asset)?,
            module: xor_option(self.module, other.module)?,
        })
    }

    /// Overrides references of `self` with references of `other`.
    pub fn combine_override(&mut self, other: Self) {
        if other.ty.is_some() {
            self.ty = other.ty;
        }
        if other.asset.is_some() {
            self.asset = other.asset;
        }
        if other.module.is_some() {
            self.module = other.module;
        }
    }
}

/// `CombinedPathReference` for `EarlySymbols` `uses`. Distinguishes between local and top level objects.
#[derive(Default, Clone, Debug)]
struct EarlyUseReference {
    ty: Option<TypeId>,
    asset: Option<(Option<TypeId>, ObjectPath)>,
    module: Option<TypePath>,
}

impl EarlyUseReference {
    /// Take the exclusive properties of `self` and `other`, essentially "xor"ing them together by producing
    /// the combined result where each field where both are `Some` are `None`.
    pub fn combined(self, other: Self) -> Option<Self> {
        Some(Self {
            ty: xor_option(self.ty, other.ty)?,
            asset: xor_option(self.asset, other.asset)?,
            module: xor_option(self.module, other.module)?,
        })
    }

    /// Overrides references of `self` with references of `other`.
    pub fn combine_override(&mut self, other: Self) {
        if other.ty.is_some() {
            self.ty = other.ty;
        }
        if other.asset.is_some() {
            self.asset = other.asset;
        }
        if other.module.is_some() {
            self.module = other.module;
        }
    }
}

impl From<PathReference> for UseReference {
    fn from(reference: PathReference) -> Self {
        Self {
            ty: reference.ty,
            asset: reference
                .asset
                .map(|(ty, path)| (ty, ObjectPath::Top(path))),
            module: reference.module,
        }
    }
}

impl From<CombinedPathReference> for EarlyUseReference {
    fn from(reference: CombinedPathReference) -> Self {
        Self {
            ty: reference.ty,
            asset: reference
                .asset
                .map(|(ty, path)| (ty, ObjectPath::Top(path))),
            module: reference.module,
        }
    }
}

impl From<UseReference> for ErrorPathReference {
    fn from(reference: UseReference) -> Self {
        Self {
            ty: reference.ty.is_some(),
            asset: reference.asset.is_some(),
            module: reference.module.is_some(),
        }
    }
}

impl From<EarlyUseReference> for ErrorPathReference {
    fn from(reference: EarlyUseReference) -> Self {
        Self {
            ty: reference.ty.is_some(),
            asset: reference.asset.is_some(),
            module: reference.module.is_some(),
        }
    }
}

/// Representation of item names available in the current module.
///
/// There are multiple namespaces: types, assets (i.e. values defined in bauble), and modules.
pub(crate) struct Symbols<'a> {
    /// Context for looking up things referenced by full path.
    pub(super) ctx: &'a BaubleContext,
    /// Map of identifiers to path references.
    uses: HashMap<TypePathElem, UseReference>,
}

impl<'a> Symbols<'a> {
    pub fn new(ctx: &'a BaubleContext) -> Self {
        Self {
            ctx,
            uses: HashMap::default(),
        }
    }

    fn add_ref(
        &mut self,
        ident: TypePathElem,
        reference: impl Into<UseReference>,
    ) -> std::result::Result<(), ConversionError> {
        let r = self.uses.entry(ident.clone()).or_default();

        *r = r
            .clone()
            .combined(reference.into())
            .ok_or(ConversionError::AmbiguousUse { ident })?;

        Ok(())
    }

    /// Note, this can also add the top level object of the current file under its local
    /// identifier.
    pub fn add_local_object(
        &mut self,
        ident: TypePathElem,
        ty: TypeId,
        full_path: TypePath,
    ) -> std::result::Result<(), ConversionError> {
        let path = if ident.as_str() == crate::object_path::TOP_LEVEL_IDENTIFIER {
            ObjectPath::Top(full_path)
        } else {
            ObjectPath::Local(full_path)
        };
        self.add_ref(
            ident,
            UseReference {
                ty: None,
                asset: Some((ty, path)),
                module: None,
            },
        )
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
                                    path_ref: None,
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
                            path_ref: None,
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
                            path_ref: None,
                            kind: RefKind::Any,
                        }))
                        .spanned(end.span));
                    }
                }
                PathTreeEnd::PathEnd(PathEnd::WithIdent(ident)) => {
                    let path_end =
                        TypePathElem::new(ident.as_str()).map_err(|e| e.spanned(ident.span))?;
                    if let Some(reference) = this
                        .ctx
                        .ref_with_ident(leading.borrow(), path_end)
                        .map_err(|e| e.spanned(ident.span))?
                    {
                        this.add_ref(path_end.to_owned(), reference)
                            .map_err(|e| e.spanned(ident.span))?;
                    } else {
                        return Err(ConversionError::RefError(Box::new(RefError {
                            uses: None,
                            path: PathKind::Indirect(leading, path_end.to_owned()),
                            path_ref: None,
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
                    path_ref: None,
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
                    path_ref: None,
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
                        path_ref: None,
                        kind: RefKind::Module,
                    }))
                    .spanned(ident.span));
                }
            }
        }

        let path = match &raw_path.last.value {
            PathEnd::WithIdent(ident) => PathKind::Indirect(
                leading,
                TypePathElem::new(ident.to_string()).map_err(|p| p.spanned(raw_path.span()))?,
            ),
            PathEnd::Ident(ident) => {
                leading
                    .push_str(ident.as_str())
                    .map_err(|p| p.spanned(raw_path.span()))?;
                PathKind::Direct(leading)
            }
            PathEnd::WithIdentGeneric(ident, generic) => {
                if !matches!(kind, ResolveKind::Type) {
                    return Err(generic_with_non_type_error(raw_path));
                }
                let generic = self.resolve_path(&generic.value, ResolveKind::Type)?;
                let inner_path = match &generic.value {
                    PathKind::Direct(generic) => {
                        if let Some(r) = self.uses.get(generic.as_str())
                            && let Some(ty) = r.ty
                        {
                            &self.ctx.type_registry().key_type(ty).meta.path
                        } else {
                            generic
                        }
                    }
                    PathKind::Indirect(_, _) => {
                        return Err(generic_param_using_with_ident(generic.span));
                    }
                };
                PathKind::Indirect(
                    leading,
                    TypePathElem::new(format!("{ident}<{inner_path}>"))
                        .map_err(|p| p.spanned(raw_path.span()))?,
                )
            }
            PathEnd::IdentGeneric(ident, generic) => {
                if !matches!(kind, ResolveKind::Type) {
                    return Err(generic_with_non_type_error(raw_path));
                }

                // The outer type and inner parameter in generic types need to be fully expanded
                // based on `uses` here (since the resolved path for a concrete instance of the
                // generic type only makes sense to lookup via full paths in the context and not
                // via `uses`).

                // Note: We could use `resolve_type` for the parameter to simplify computing
                // `inner_path` except there are cases with reference types where the ref type
                // isn't registered until an asset with the type is registered. So if there was
                // `MyGeneric<Ref<MyType>>`, then calling `resolve_type` here could fail.
                let generic = self.resolve_path(&generic.value, ResolveKind::Type)?;
                let inner_path = match &generic.value {
                    PathKind::Direct(generic) => {
                        if let Some(r) = self.uses.get(generic.as_str())
                            && let Some(ty) = r.ty
                        {
                            &self.ctx.type_registry().key_type(ty).meta.path
                        } else {
                            generic
                        }
                    }
                    PathKind::Indirect(_, _) => {
                        return Err(generic_param_using_with_ident(generic.span));
                    }
                };

                let path = if leading.is_empty()
                    && let Some(r) = self.uses.get(ident.as_str())
                    && let Some(ty) = r.ty
                {
                    let outer_path = &self.ctx.type_registry().key_type(ty).meta.path;
                    TypePath::new(format!("{outer_path}<{inner_path}>"))
                        .map_err(|p| p.spanned(raw_path.span()))?
                } else {
                    leading
                        .push_str(&format!("{ident}<{inner_path}>"))
                        .map_err(|p| p.spanned(raw_path.span()))?;
                    leading
                };
                PathKind::Direct(path)
            }
        };
        Ok(path.spanned(raw_path.span()))
    }

    fn resolve_item(
        &self,
        raw_path: &Path,
        kind: ResolveKind,
    ) -> Result<(Cow<'_, UseReference>, PathKind)> {
        let path = self.resolve_path(raw_path, kind)?;

        let reference = match &path.value {
            PathKind::Direct(path) => {
                let r_uses = self.uses.get(path.as_str());
                let r_ctx = self.ctx.get_ref(path.borrow()).map(UseReference::from);
                // There can be overlap between items that are children of the root of ctx and the
                // uses here. Items from uses take priority and collisions aren't errors.
                if let Some(r_uses) = r_uses {
                    Some(if let Some(mut r_ctx) = r_ctx {
                        r_ctx.combine_override(r_uses.clone());
                        Cow::Owned(r_ctx)
                    } else {
                        Cow::Borrowed(r_uses)
                    })
                } else {
                    r_ctx.map(Cow::Owned)
                }
            }
            PathKind::Indirect(path, ident) => self
                .ctx
                .ref_with_ident(path.borrow(), ident.borrow())
                .map_err(|e| e.spanned(raw_path.span()))?
                .map(UseReference::from)
                .map(Cow::Owned),
        };

        if let Some(reference) = reference {
            Ok((reference, path.value))
        } else {
            Err(if let PathKind::Direct(path) = &*path
                && let Some((leading, ident)) = path.get_end()
                && let Some(r) = self.ctx.get_ref(leading)
                && let Some(ty) = r.ty
                && matches!(
                    self.ctx.type_registry().key_type(ty).kind,
                    types::TypeKind::Enum { .. } | types::TypeKind::Or(_)
                ) {
                ConversionError::UnknownVariant {
                    variant: ident.to_owned().spanned(raw_path.last.span),
                    ty,
                }
            } else {
                ConversionError::RefError(Box::new(RefError {
                    uses: Some(self.uses.keys().cloned().collect()),
                    path: path.value.clone(),
                    path_ref: None,
                    kind: kind.into(),
                }))
            }
            .spanned(raw_path.span()))
        }
    }

    pub fn resolve_asset(&self, path: &Path) -> Result<(TypeId, ObjectPath)> {
        let (item, resolved_path) = self.resolve_item(path, ResolveKind::Asset)?;
        let item = item.into_owned();

        if let Some((ty, path)) = item.asset {
            Ok((ty, path))
        } else {
            Err(ConversionError::RefError(Box::new(RefError {
                uses: Some(self.uses.keys().cloned().collect()),
                path: resolved_path,
                path_ref: Some(item.into()),
                kind: RefKind::Asset,
            }))
            .spanned(path.span()))
        }
    }

    pub fn resolve_type(&self, path: &Path) -> Result<TypeId> {
        let (item, resolved_path) = self.resolve_item(path, ResolveKind::Type)?;

        if let Some(ty) = item.ty {
            Ok(ty)
        } else {
            Err(ConversionError::RefError(Box::new(RefError {
                uses: Some(self.uses.keys().cloned().collect()),
                path: resolved_path,
                path_ref: Some(item.into_owned().into()),
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
    /// Context for local objects.
    local_ctx: &'a mut LocalContext,
    /// Map of identifiers to path references.
    uses: HashMap<TypePathElem, EarlyUseReference>,
}

impl<'a, 'b> EarlySymbols<'a, 'b> {
    pub fn new(ctx: &'a mut EarlyContext<'b>, local_ctx: &'a mut LocalContext) -> Self {
        Self {
            ctx,
            local_ctx,
            uses: HashMap::default(),
        }
    }

    /// Get contexts for registering new assets.
    pub fn ctx_for_register(&mut self) -> (&mut BaubleContext, &mut LocalContext) {
        (self.ctx.ctx, self.local_ctx)
    }

    fn add_ref(
        &mut self,
        ident: TypePathElem,
        reference: impl Into<EarlyUseReference>,
    ) -> std::result::Result<(), ConversionError> {
        let r = self.uses.entry(ident.clone()).or_default();

        *r = r
            .clone()
            .combined(reference.into())
            .ok_or(ConversionError::AmbiguousUse { ident })?;

        Ok(())
    }

    /// Note, this can also add the top level object of the current file under its local
    /// identifier.
    pub fn add_local_object(
        &mut self,
        ident: TypePathElem,
        ty: Option<TypeId>,
        full_path: TypePath,
    ) -> std::result::Result<(), ConversionError> {
        let path = if ident.as_str() == crate::object_path::TOP_LEVEL_IDENTIFIER {
            ObjectPath::Top(full_path)
        } else {
            ObjectPath::Local(full_path)
        };
        self.add_ref(
            ident,
            EarlyUseReference {
                ty: None,
                asset: Some((ty, path)),
                module: None,
            },
        )
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
                                    path_ref: None,
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
                            path_ref: None,
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
                            path_ref: None,
                            kind: RefKind::Any,
                        }))
                        .spanned(end.span));
                    }
                }
                PathTreeEnd::PathEnd(PathEnd::WithIdent(ident)) => {
                    let path_end =
                        TypePathElem::new(ident.as_str()).map_err(|e| e.spanned(ident.span))?;
                    if let Some(reference) = this
                        .ctx
                        .ref_with_ident(leading.borrow(), path_end)
                        .map_err(|e| e.spanned(ident.span))?
                    {
                        this.add_ref(path_end.to_owned(), reference)
                            .map_err(|e| e.spanned(ident.span))?;
                    } else {
                        return Err(ConversionError::RefError(Box::new(RefError {
                            uses: None,
                            path: PathKind::Indirect(leading, path_end.to_owned()),
                            path_ref: None,
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
                    path_ref: None,
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
                    path_ref: None,
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
                        path_ref: None,
                        kind: RefKind::Module,
                    }))
                    .spanned(ident.span));
                }
            }
        }

        let path = match &raw_path.last.value {
            PathEnd::WithIdent(ident) => PathKind::Indirect(
                leading,
                TypePathElem::new(ident.to_string()).map_err(|p| p.spanned(raw_path.span()))?,
            ),
            PathEnd::Ident(ident) => {
                leading
                    .push_str(ident.as_str())
                    .map_err(|p| p.spanned(raw_path.span()))?;
                PathKind::Direct(leading)
            }
            PathEnd::WithIdentGeneric(ident, generic) => {
                if !matches!(kind, ResolveKind::Type) {
                    return Err(generic_with_non_type_error(raw_path));
                }

                let generic = self.resolve_path(&generic.value, ResolveKind::Type)?;
                let inner_path = match &generic.value {
                    PathKind::Direct(generic) => {
                        if let Some(r) = self.uses.get(generic.as_str())
                            && let Some(ty) = r.ty
                        {
                            &self.ctx.type_registry().key_type(ty).meta.path
                        } else {
                            generic
                        }
                    }
                    PathKind::Indirect(_, _) => {
                        return Err(generic_param_using_with_ident(generic.span));
                    }
                };

                PathKind::Indirect(
                    leading,
                    TypePathElem::new(format!("{ident}<{inner_path}>"))
                        .map_err(|p| p.spanned(raw_path.span()))?,
                )
            }
            PathEnd::IdentGeneric(ident, generic) => {
                if !matches!(kind, ResolveKind::Type) {
                    return Err(generic_with_non_type_error(raw_path));
                }

                let generic = self.resolve_path(&generic.value, ResolveKind::Type)?;
                let inner_path = match &generic.value {
                    PathKind::Direct(generic) => {
                        if let Some(r) = self.uses.get(generic.as_str())
                            && let Some(ty) = r.ty
                        {
                            &self.ctx.type_registry().key_type(ty).meta.path
                        } else {
                            generic
                        }
                    }
                    PathKind::Indirect(_, _) => {
                        return Err(generic_param_using_with_ident(generic.span));
                    }
                };

                let path = if leading.is_empty()
                    && let Some(r) = self.uses.get(ident.as_str())
                    && let Some(ty) = r.ty
                {
                    let outer_path = &self.ctx.type_registry().key_type(ty).meta.path;
                    TypePath::new(format!("{outer_path}<{inner_path}>"))
                        .map_err(|p| p.spanned(raw_path.span()))?
                } else {
                    leading
                        .push_str(&format!("{ident}<{inner_path}>"))
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
    ) -> Result<(Cow<'_, EarlyUseReference>, PathKind)> {
        let path = self.resolve_path(raw_path, kind)?;

        let reference = match &path.value {
            PathKind::Direct(path) => {
                let r_uses = self.uses.get(path.as_str());
                let r_ctx = self.ctx.get_ref(path.borrow()).map(EarlyUseReference::from);
                // There can be overlap between items that are children of the root of ctx and the
                // uses here. Items from uses take priority and collisions aren't errors.
                if let Some(r_uses) = r_uses {
                    Some(if let Some(mut r_ctx) = r_ctx {
                        r_ctx.combine_override(r_uses.clone());
                        Cow::Owned(r_ctx)
                    } else {
                        Cow::Borrowed(r_uses)
                    })
                } else {
                    r_ctx.map(Cow::Owned)
                }
            }
            PathKind::Indirect(path, ident) => self
                .ctx
                .ref_with_ident(path.borrow(), ident.borrow())
                .map_err(|e| e.spanned(raw_path.span()))?
                .map(EarlyUseReference::from)
                .map(Cow::Owned),
        };

        if let Some(reference) = reference {
            Ok((reference, path.value))
        } else {
            Err(if let PathKind::Direct(path) = &*path
                && let Some((leading, ident)) = path.get_end()
                && let Some(r) = self.ctx.get_ref(leading)
                && let Some(ty) = r.ty
                && matches!(
                    self.ctx.type_registry().key_type(ty).kind,
                    types::TypeKind::Enum { .. } | types::TypeKind::Or(_)
                ) {
                ConversionError::UnknownVariant {
                    variant: ident.to_owned().spanned(raw_path.last.span),
                    ty,
                }
            } else {
                ConversionError::RefError(Box::new(RefError {
                    uses: Some(self.uses.keys().cloned().collect()),
                    path: path.value.clone(),
                    path_ref: None,
                    kind: kind.into(),
                }))
            }
            .spanned(raw_path.span()))
        }
    }

    /// Resolves full path without requiring that the type has been registered yet.
    ///
    /// Useful to later lookup the type when `EarlySymbols` is no longer available.
    pub fn resolve_full_path_for_type(&self, path: &Path) -> Result<Spanned<PathKind>> {
        let path = self.resolve_path(path, ResolveKind::Type)?;
        Ok(match path.value {
            PathKind::Direct(path) => {
                if let Some(r) = self.uses.get(path.as_str())
                    && let Some(ty) = r.ty
                {
                    PathKind::Direct(self.ctx.type_registry().key_type(ty).meta.path.clone())
                } else {
                    PathKind::Direct(path)
                }
            }
            p @ PathKind::Indirect(_, _) => p,
        }
        .spanned(path.span))
    }

    /// Note, if an asset isn't registered in `BaubleContext` yet, its type will be unknown.
    pub fn resolve_asset(&self, path: &Path) -> Result<(Option<TypeId>, ObjectPath)> {
        let (item, resolved_path) = self.resolve_item(path, ResolveKind::Asset)?;
        let item = item.into_owned();

        if let Some((mut ty, path)) = item.asset {
            // Once an asset is registered with its type, the path reference stored in `uses` will
            // be outdated since it won't include the type (an up-to-date value isn't essential but
            // will lead to fewer assets to process in resolve_delayed).
            if ty.is_none() {
                match &path {
                    ObjectPath::Top(path) => {
                        ty = self
                            .ctx
                            .get_ref(path.borrow())
                            .and_then(|r| r.asset)
                            .expect("This asset is in uses, so it will exist in ctx.")
                            .0;
                    }
                    ObjectPath::Local(path) => {
                        ty = self.local_ctx.get(path.borrow());
                    }
                    ObjectPath::Inline(_) => {
                        #[cfg(debug_assertions)]
                        unreachable!();
                    }
                }
            }
            Ok((ty, path))
        } else {
            Err(ConversionError::RefError(Box::new(RefError {
                uses: Some(self.uses.keys().cloned().collect()),
                path: resolved_path,
                path_ref: Some(item.into()),
                kind: RefKind::Asset,
            }))
            .spanned(path.span()))
        }
    }

    pub fn resolve_type(&self, path: &Path) -> Result<TypeId> {
        let (item, resolved_path) = self.resolve_item(path, ResolveKind::Type)?;

        if let Some(ty) = item.ty {
            Ok(ty)
        } else {
            Err(ConversionError::RefError(Box::new(RefError {
                uses: Some(self.uses.keys().cloned().collect()),
                path: resolved_path,
                path_ref: Some(item.into_owned().into()),
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
        self.resolve_asset(path).map(|(ty, _path)| ty)
    }

    fn resolve_type(&self, path: &Path) -> Result<TypeId> {
        self.resolve_type(path)
    }

    fn type_registry(&self) -> &TypeRegistry {
        self.ctx.type_registry()
    }
}

fn xor_option<T>(a: Option<T>, b: Option<T>) -> Option<Option<T>> {
    match (a, b) {
        (Some(_), Some(_)) => None,
        (Some(t), None) | (None, Some(t)) => Some(Some(t)),
        (None, None) => Some(None),
    }
}
