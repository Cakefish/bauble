use std::{borrow::Cow, collections::HashMap};

use crate::{
    BaubleContext, CustomError,
    context::PathReference,
    parse::{Path, PathEnd, PathTreeEnd, PathTreeNode},
    path::{TypePath, TypePathElem},
    spanned::{SpanExt, Spanned},
    types::{self, TypeId},
};

use super::{ConversionError, PathKind, RefError, RefKind, Result};

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

    pub fn add(&mut self, symbols: Symbols) {
        // TODO: what about conflicting entries?
        self.uses.extend(symbols.uses)
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
                                    path_ref: PathReference::empty(),
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
                            path_ref: PathReference::empty(),
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
                            path_ref: PathReference::empty(),
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
                            path_ref: PathReference::empty(),
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
                    path_ref: PathReference::empty(),
                    kind: RefKind::Module,
                }))
                .spanned(l.span));
            }
        }
        add_use_inner(self, leading, &use_path.end)
    }

    pub fn get_module(&self, ident: &str) -> Option<TypePath> {
        self.uses
            .get(ident)
            .and_then(|reference| reference.module.clone())
    }

    pub fn resolve_path(&self, raw_path: &Path) -> Result<Spanned<PathKind>> {
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
                    path_ref: PathReference::empty(),
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
                        path_ref: PathReference::empty(),
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
                let generic = self.resolve_path(&generic.value)?;
                PathKind::Indirect(
                    leading,
                    TypePathElem::new(format!("{ident}<{generic}>"))
                        .map_err(|p| p.spanned(raw_path.span()))?,
                )
            }
            PathEnd::IdentGeneric(ident, generic) => {
                let generic = self.resolve_path(&generic.value)?;
                leading
                    .push_str(&format!("{ident}<{generic}>"))
                    .map_err(|p| p.spanned(raw_path.span()))?;
                PathKind::Direct(leading)
            }
        };
        Ok(path.spanned(raw_path.span()))
    }

    pub fn resolve_item(
        &self,
        raw_path: &Path,
        ref_kind: RefKind,
    ) -> Result<Cow<'_, PathReference>> {
        fn resolve_path(
            symbols: &Symbols,
            raw_path: &Path,
            ref_kind: RefKind,
        ) -> Result<Spanned<PathKind>> {
            let raw_path_split = raw_path.split_generic();
            let is_generic = raw_path_split.is_some();
            let (path, &generic) = raw_path_split
                .as_ref()
                .map(|(l, r)| (l, r))
                .unwrap_or((raw_path, &raw_path));

            let path = symbols.resolve_path(path)?;

            Ok(if matches!(ref_kind, RefKind::Type) {
                match path.value {
                    PathKind::Direct(type_path) => {
                        if let Some(r) = symbols.uses.get(type_path.as_str())
                            && let Some(ty) = r.ty
                        {
                            let path = &symbols.ctx.type_registry().key_type(ty).meta.path;
                            if is_generic {
                                let generic = resolve_path(symbols, generic, ref_kind)?;
                                PathKind::Direct(
                                    TypePath::new(format!("{path}<{generic}>")).unwrap(),
                                )
                            } else {
                                PathKind::Direct(TypePath::new(path.to_string()).unwrap())
                            }
                        } else if is_generic {
                            let generic = resolve_path(symbols, generic, ref_kind)?;
                            PathKind::Direct(
                                TypePath::new(format!("{type_path}<{generic}>")).unwrap(),
                            )
                        } else {
                            PathKind::Direct(TypePath::new(format!("{type_path}")).unwrap())
                        }
                    }
                    PathKind::Indirect(type_path, type_path_elem) => {
                        if is_generic {
                            let generic = resolve_path(symbols, generic, ref_kind)?;
                            PathKind::Indirect(
                                type_path,
                                TypePathElem::new(format!("{type_path_elem}<{generic}>")).unwrap(),
                            )
                        } else {
                            PathKind::Indirect(type_path, type_path_elem)
                        }
                    }
                }
                .spanned(path.span)
            } else {
                path
            })
        }

        let path = resolve_path(self, raw_path, ref_kind)?;

        let reference = match &path.value {
            PathKind::Direct(path) => {
                if let Some(r) = self.uses.get(path.as_str()) {
                    Some(Cow::Borrowed(r))
                } else {
                    self.ctx.get_ref(path.borrow()).map(Cow::Owned)
                }
            }
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
                    uses: Some(self.uses.clone()),
                    path: path.value.clone(),
                    path_ref: PathReference::empty(),
                    kind: ref_kind,
                }))
            }
            .spanned(raw_path.span())
        })
    }

    pub fn resolve_asset(&self, path: &Path) -> Result<(TypeId, TypePath)> {
        let item = self.resolve_item(path, RefKind::Asset)?.into_owned();

        if let Some((ty, path, _kind)) = item.asset {
            Ok((ty, path))
        } else {
            Err(ConversionError::RefError(Box::new(RefError {
                uses: Some(self.uses.clone()),
                path: self.resolve_path(path)?.value,
                path_ref: item,
                kind: RefKind::Asset,
            }))
            .spanned(path.span()))
        }
    }

    pub fn resolve_type(&self, path: &Path) -> Result<TypeId> {
        let item = self.resolve_item(path, RefKind::Type)?;

        if let Some(ty) = item.ty {
            Ok(ty)
        } else {
            Err(ConversionError::RefError(Box::new(RefError {
                uses: Some(self.uses.clone()),
                path: self.resolve_path(path)?.value,
                path_ref: item.into_owned(),
                kind: RefKind::Type,
            }))
            .spanned(path.span()))
        }
    }
}
