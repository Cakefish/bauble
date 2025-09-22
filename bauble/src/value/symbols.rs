use std::{borrow::Cow, collections::HashMap};

use crate::{
    BaubleContext,
    context::PathReference,
    parse::{Path, PathEnd, PathTreeEnd, Use},
    path::{TypePath, TypePathElem},
    spanned::{SpanExt, Spanned},
    types::{self, TypeId},
};

use super::{ConversionError, CopyVal, PathKind, RefError, RefKind, Result};

#[derive(Clone, Debug)]
pub(super) enum RefCopy {
    Unresolved,
    Resolved(CopyVal),
    Ref(PathReference),
}

impl Default for RefCopy {
    fn default() -> Self {
        Self::Ref(Default::default())
    }
}

impl RefCopy {
    /// # Panics
    /// Panics if self isn't a reference.
    fn unwrap_ref(&self) -> &PathReference {
        match self {
            RefCopy::Ref(r) => r,
            RefCopy::Unresolved | RefCopy::Resolved(_) => panic!("Not a reference"),
        }
    }

    fn add(self, other: PathReference) -> Option<Self> {
        match self {
            RefCopy::Unresolved | RefCopy::Resolved(_) => None,
            RefCopy::Ref(reference) => Some(RefCopy::Ref(reference.combined(other)?)),
        }
    }
}

#[derive(Clone)]
pub(crate) struct Symbols<'a> {
    pub(super) ctx: &'a BaubleContext,
    pub(super) uses: HashMap<TypePathElem, RefCopy>,
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
            .add(reference)
            .ok_or(ConversionError::AmbiguousUse { ident })?;

        Ok(())
    }

    pub fn add(&mut self, symbols: Symbols) {
        self.uses.extend(symbols.uses)
    }

    pub fn add_use(&mut self, use_: &Use) -> Result<()> {
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
                PathTreeEnd::PathEnd(PathEnd::IdentGeneric(ident, gen_path)) => {
                    let path_end =
                        TypePathElem::new(ident.as_str()).map_err(|e| e.spanned(ident.span))?;
                    let mut path = leading.join(&path_end);
                    path.push_generic(
                        TypePath::new(gen_path.to_string())
                            .map_err(|e| Spanned::new(gen_path.span, e))?
                            .borrow(),
                    )
                    .map_err(|e| e.spanned(gen_path.span))?;
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
                PathTreeEnd::PathEnd(PathEnd::WithIdentGeneric(ident, gen_path)) => {
                    let fmt = format!("{ident}<{gen_path}>",);
                    let path_end =
                        TypePathElem::new(fmt.as_str()).map_err(|e| e.spanned(ident.span))?;
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
            }
            Ok(())
        }

        let mut leading = TypePath::empty();
        for l in use_.leading.iter() {
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
        add_use_inner(self, leading, &use_.end)
    }

    pub(super) fn try_resolve_copy<'b>(
        &'b self,
        ident: &str,
    ) -> Option<(TypePathElem<&'b str>, Option<&'b CopyVal>)> {
        let (key, value) = self.uses.get_key_value(ident)?;
        match value {
            RefCopy::Unresolved => Some((key.borrow(), None)),
            RefCopy::Resolved(val) => Some((key.borrow(), Some(val))),
            RefCopy::Ref(_) => None,
        }
    }

    pub fn get_module(&self, ident: &str) -> Option<TypePath> {
        self.uses
            .get(ident)
            .and_then(|reference| reference.unwrap_ref().module.clone())
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
            PathEnd::WithIdentGeneric(ident, path) => PathKind::Indirect(
                leading,
                TypePathElem::new(format!("{ident}<{path}>"))
                    .map_err(|p| p.spanned(raw_path.span()))?,
            ),
            PathEnd::IdentGeneric(ident, path) => {
                leading
                    .push_str(ident.as_str())
                    .map_err(|p| p.spanned(raw_path.span()))?;
                leading
                    .push_generic(
                        TypePath::new(path.to_string())
                            .map_err(|e| Spanned::new(path.span, e))?
                            .borrow(),
                    )
                    .map_err(|p| p.spanned(raw_path.span()))?;
                PathKind::Direct(leading)
            }
        };
        Ok(path.spanned(raw_path.span()))
    }

    pub fn resolve_item(&self, raw_path: &Path, ref_kind: RefKind) -> Result<Cow<PathReference>> {
        // In case the type is generic, split the type into its base path and
        // the inner generic argument.
        if matches!(ref_kind, RefKind::Type)
            && let Some((ty_path, ..)) = raw_path.split_generic()
        {
            return self.resolve_item(&ty_path, RefKind::Type);
        }

        let path = self.resolve_path(raw_path)?;
        match &path.value {
            PathKind::Direct(path) => {
                if let Some(RefCopy::Ref(r)) = self.uses.get(path.as_str()) {
                    return Ok(Cow::Borrowed(r));
                } else {
                    self.ctx.get_ref(path.borrow())
                }
            }
            PathKind::Indirect(path, ident) => {
                self.ctx.ref_with_ident(path.borrow(), ident.borrow())
            }
        }
        .ok_or_else(|| {
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
        .map(Cow::Owned)
    }

    pub fn resolve_asset(&self, path: &Path) -> Result<(TypeId, TypePath)> {
        let item = self.resolve_item(path, RefKind::Asset)?;

        item.asset.clone().ok_or(
            ConversionError::RefError(Box::new(RefError {
                uses: Some(self.uses.clone()),
                path: self.resolve_path(path)?.value,
                path_ref: item.into_owned(),
                kind: RefKind::Asset,
            }))
            .spanned(path.span()),
        )
    }

    pub fn resolve_type(&self, path: &Path) -> Result<TypeId> {
        let item = self.resolve_item(path, RefKind::Type)?;

        item.ty.ok_or(
            ConversionError::RefError(Box::new(RefError {
                uses: Some(self.uses.clone()),
                path: self.resolve_path(path)?.value,
                path_ref: item.into_owned(),
                kind: RefKind::Type,
            }))
            .spanned(path.span()),
        )
    }
}
