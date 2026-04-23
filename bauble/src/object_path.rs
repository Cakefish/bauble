//! Bauble objects can either be top-level, local, or inline.
//!
//! For a reference to an object, this is known once the full path to an
//! object is resolved during value loading. That resolved path is represented using
//! [`ObjectPath`].
//!
//! When written in a file the top level object of each file uses a special identifier
//! [`TOP_LEVEL_IDENTIFIER`].
//!
//! The [`ObjectPathKey`] trait exists to work past limitations in existing `HashMap` trait bounds
//! on keys so that borrowed versions of `ObjectPath` can be used to lookup values in a `HashMap`
//! using owned `ObjectPath` keys.

use crate::types::path::TypePath;
use std::hash::{Hash, Hasher};

/// Special cased identifier that is required and only allowed for the first asset in a file
/// (i.e. the top level asset that is named after the file).
pub const TOP_LEVEL_IDENTIFIER: &str = "0";

/// Full path to a bauble object (or external asset).
///
/// Path format documented in [`TypePath`].
#[derive(Copy, Clone, Debug)]
pub enum ObjectPath<S = String> {
    /// Top-level object or external asset. There is at most one per file.
    ///
    /// This shares the path of the containing file and uses the special identifier
    /// [`TOP_LEVEL_IDENTIFIER`].
    ///
    /// These objects are generally intended to be globally visible and referencable.
    Top(TypePath<S>),
    /// Local object.
    ///
    /// All objects that aren't considered top level or inline. These can only be referenced from
    /// the same file.
    Local(TypePath<S>),
    /// Object defined inline in the definition of the parent object that references it.
    ///
    /// This is implicitly only referencable by the parent object.
    Inline(TypePath<S>),
}

impl<S: AsRef<str>> ObjectPath<S> {
    /// Identifier that is used for this object when it appears in a bauble file.
    ///
    /// `None` for inline objects and for local objects that have an empty path.
    pub fn ident(&self) -> Option<&str> {
        match self {
            Self::Top(_) => Some(TOP_LEVEL_IDENTIFIER),
            Self::Local(path) => path.get_end().map(|(_, end)| end.into_str()),
            Self::Inline(_) => None,
        }
    }

    /// Get the file path that this object belongs to.
    pub fn file_path(&self) -> TypePath<&str> {
        self.borrow().into_file_path()
    }

    /// Gets a borrowed version of the path.
    pub fn borrow(&self) -> ObjectPath<&str> {
        match self {
            Self::Top(path) => ObjectPath::Top(path.borrow()),
            Self::Local(path) => ObjectPath::Local(path.borrow()),
            Self::Inline(path) => ObjectPath::Inline(path.borrow()),
        }
    }

    /// Convert this into an owned path.
    pub fn to_owned(&self) -> ObjectPath {
        match self {
            Self::Top(path) => ObjectPath::Top(path.to_owned()),
            Self::Local(path) => ObjectPath::Local(path.to_owned()),
            Self::Inline(path) => ObjectPath::Inline(path.to_owned()),
        }
    }

    /// Casts reference to trait object that `ObjectPath` implements `Borrow` for.
    ///
    /// This useful to mix owned and borrowed paths when using `ObjectPath` as a key type in a map
    /// that requires the `Borrow` trait.
    pub fn as_key(&self) -> &dyn ObjectPathKey {
        self
    }
}

impl<'a> ObjectPath<&'a str> {
    /// Get the file path that this object belongs to.
    pub fn into_file_path(&self) -> TypePath<&'a str> {
        match *self {
            Self::Top(path) => path,
            Self::Local(path) => path
                .split_end()
                .map_or(TypePath::empty(), |(prefix, _)| prefix),
            Self::Inline(path) => path
                .split_end()
                .map_or(TypePath::empty(), |(prefix, _)| prefix),
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum ObjectPathKeyImpl<'a> {
    Top(TypePath<&'a str>),
    Local(TypePath<&'a str>),
    Inline(TypePath<&'a str>),
}

impl<'a> From<ObjectPath<&'a str>> for ObjectPathKeyImpl<'a> {
    fn from(path: ObjectPath<&'a str>) -> Self {
        match path {
            ObjectPath::Top(path) => Self::Top(path),
            ObjectPath::Local(path) => Self::Local(path),
            ObjectPath::Inline(path) => Self::Inline(path),
        }
    }
}

impl<S: AsRef<str>> Hash for ObjectPath<S> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        ObjectPathKeyImpl::from(self.borrow()).hash(state)
    }
}

impl<S: AsRef<str>> PartialEq for ObjectPath<S> {
    fn eq(&self, other: &Self) -> bool {
        ObjectPathKeyImpl::from(self.borrow()) == ObjectPathKeyImpl::from(other.borrow())
    }
}

impl<S: AsRef<str>> Eq for ObjectPath<S> {}

impl<S: AsRef<str>> PartialOrd for ObjectPath<S> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<S: AsRef<str>> Ord for ObjectPath<S> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        ObjectPathKeyImpl::from(self.borrow()).cmp(&ObjectPathKeyImpl::from(other.borrow()))
    }
}

/// Trait that allows mixing borrowed and owned paths when using them as keys for methods like
/// `HashMap::get`.
///
/// See https://github.com/rust-lang/libs-team/issues/699#issue-3643767617
///
/// Works around lack of https://github.com/rust-lang/rust/issues/145986
pub trait ObjectPathKey {
    #[doc(hidden)]
    fn key(&self) -> ObjectPath<&str>;
}

impl<S: AsRef<str>> ObjectPathKey for ObjectPath<S> {
    fn key(&self) -> ObjectPath<&str> {
        self.borrow()
    }
}

impl<'a, S: AsRef<str> + 'a> std::borrow::Borrow<dyn ObjectPathKey + 'a> for ObjectPath<S> {
    fn borrow(&self) -> &(dyn ObjectPathKey + 'a) {
        self
    }
}

impl Hash for dyn ObjectPathKey + '_ {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.key().hash(state)
    }
}

impl PartialEq for dyn ObjectPathKey + '_ {
    fn eq(&self, other: &Self) -> bool {
        self.key() == other.key()
    }
}

impl Eq for dyn ObjectPathKey + '_ {}
