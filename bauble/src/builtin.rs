use crate::{
    Bauble, BaubleAllocator, ToRustErrorKind, Val, Value,
    path::TypePath,
    types::{Type, TypeRegistry},
};
use std::{cell::UnsafeCell, fmt::Debug, marker::PhantomData};

/// The builtin reference type.
///
/// Corresponds to a reference to `T` in Bauble.
///
/// `S` is the inner representation used for `TypePath`.
pub struct Ref<T, S = String> {
    /// The path to the referenced asset.
    pub path: TypePath<S>,
    /// Invariant over `T`.
    _mark: PhantomData<UnsafeCell<T>>,
}

impl<T, S> Ref<T, S> {
    /// Create a reference from the specified path. The path must not be valid.
    pub fn from_path(path: TypePath<S>) -> Self {
        Self {
            path,
            _mark: PhantomData,
        }
    }
}

impl<T, S: PartialEq> PartialEq for Ref<T, S> {
    fn eq(&self, other: &Self) -> bool {
        self.path == other.path
    }
}
impl<T, S: Eq> Eq for Ref<T, S> {}

impl<T, S: Debug> Debug for Ref<T, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self.path, f)
    }
}

impl<'b, A: BaubleAllocator<'b>, T: Bauble<'b, A>> Bauble<'b, A> for Ref<T, A::TypePathInner> {
    fn builtin(registry: &mut TypeRegistry) -> Option<crate::types::TypeId> {
        let inner = registry.get_or_register_type::<T, A>();
        Some(registry.get_or_register_asset_ref(inner))
    }

    fn construct_type(_registry: &mut TypeRegistry) -> Type {
        unreachable!("This is a builtin and should never be constructed.");
    }

    fn from_bauble(
        val: Val,
        allocator: &A,
    ) -> Result<<A as BaubleAllocator<'b>>::Out<Self>, crate::ToRustError> {
        match val.value.value {
            Value::Ref(r) => Ok({
                let path = allocator.wrap_type_path(r);
                let value = Self {
                    // SAFETY: path was derived from `allocator`.
                    path: unsafe { allocator.validate(path)? },
                    _mark: PhantomData,
                };

                // SAFETY: allocator has wrapped the type path.
                unsafe { allocator.wrap(value) }
            }),
            _ => Err(Self::error(
                val.value.span,
                ToRustErrorKind::WrongType { found: val.ty },
            )),
        }
    }
}
