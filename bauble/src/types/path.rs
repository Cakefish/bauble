use std::ops::Deref;

use chumsky::text::Char;

const PATH_DELIMS: &[(char, char)] = &[('<', '>'), ('[', ']'), ('{', '}'), ('(', ')')];
const PATH_SEPERATOR: &str = "::";

/// This is a `TypePath` with the invariant that `TypePath::len() == 1`.
#[derive(Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct TypePathElem<S = String>(TypePath<S>);

impl indexmap::Equivalent<TypePathElem> for TypePathElem<&str> {
    fn equivalent(&self, key: &TypePathElem) -> bool {
        self.as_str() == key.as_str()
    }
}

impl<S: AsRef<str>> std::borrow::Borrow<str> for TypePathElem<S> {
    fn borrow(&self) -> &str {
        self.as_str()
    }
}

impl<S> From<TypePathElem<S>> for TypePath<S> {
    fn from(value: TypePathElem<S>) -> Self {
        value.0
    }
}

impl<S: AsRef<str>> std::hash::Hash for TypePathElem<S> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::hash::Hash::hash(self.as_str(), state)
    }
}

impl<S: std::fmt::Debug> std::fmt::Debug for TypePathElem<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(self.get_inner(), f)
    }
}

impl<S: AsRef<str>> std::fmt::Display for TypePathElem<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.as_str(), f)
    }
}

impl<S> Deref for TypePathElem<S> {
    type Target = TypePath<S>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<S: AsRef<str>> TryFrom<TypePath<S>> for TypePathElem<S> {
    type Error = PathError;

    fn try_from(value: TypePath<S>) -> Result<Self> {
        match value.len() {
            0 => Err(PathError::ZeroElements),
            1 => Ok(Self(value)),
            2.. => Err(PathError::TooManyElements),
        }
    }
}

impl<S: AsRef<str>> TypePathElem<S> {
    /// Creates a new path element, returns err if it's not one element.
    pub fn new(s: S) -> Result<Self> {
        let l = path_len(s.as_ref())?;
        match l {
            0 => Err(PathError::ZeroElements),
            1 => Ok(Self(TypePath(s))),
            2.. => Err(PathError::TooManyElements),
        }
    }

    /// Convert this to an owned path element.
    pub fn to_owned(&self) -> TypePathElem<String> {
        TypePathElem(self.0.to_owned())
    }

    /// Borrow this path element.
    pub fn borrow(&self) -> TypePathElem<&str> {
        TypePathElem(self.0.borrow())
    }

    /// For path elements this is always false.
    pub fn is_empty(&self) -> bool {
        false
    }

    /// For path elements this is always one.
    pub fn len(&self) -> usize {
        1
    }
}

impl<S> TypePathElem<S> {
    /// Creates a new type path elem without checking for correctness.
    ///
    /// This isn't unsafe but a lot of logic assumes a `TypePathElem` to be correct so would
    /// still cause bugs to use this incorrectly.
    pub fn new_unchecked(inner: S) -> Self {
        Self(TypePath::new_unchecked(inner))
    }

    pub fn into_inner(self) -> S {
        self.0.into_inner()
    }

    pub fn get_inner(&self) -> &S {
        self.0.get_inner()
    }

    /// This isn't unsafe but a lot of logic assumes a `TypePath` to be correct so would
    /// still cause bugs to use this incorrectly.
    pub fn get_inner_mut(&mut self) -> &mut S {
        self.0.get_inner_mut()
    }
}

/// A path seperated by `::`. I.e `this::is::a::path`
/// A path element can contain spans of delimiters, i.e `some_ident<test>`. These spans
/// can themselves contain paths like `some_ident<inner::path>` which still count as one
/// path. For example `this::is<a>::valid(path)`.
///
/// We maintain as an invariant that all paths are valid. And don't contain invalid spans
/// like `this::<is::not::a::valid)::path`.
///
/// Path elements can't be empty, but paths themselves are allowed to be empty.
#[derive(Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct TypePath<S = String>(S);

impl indexmap::Equivalent<TypePath> for TypePath<&str> {
    fn equivalent(&self, key: &TypePath) -> bool {
        self.as_str() == key.as_str()
    }
}

impl<S: AsRef<str>> std::borrow::Borrow<str> for TypePath<S> {
    fn borrow(&self) -> &str {
        self.as_str()
    }
}

impl<S: AsRef<str>> std::hash::Hash for TypePath<S> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::hash::Hash::hash(self.as_str(), state)
    }
}

impl<S: std::fmt::Debug> std::fmt::Debug for TypePath<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(self.get_inner(), f)
    }
}

impl<S: AsRef<str>> std::fmt::Display for TypePath<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.as_str(), f)
    }
}

/// An error when forming paths.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PathError {
    /// There was an empty path element, for example `foo::::bar`.
    EmptyElem(usize),
    /// A start delimiter, i.e `<`, `(`, `[`, is missing its end equivalent.
    MissingDelimiterEnd(usize),
    /// An end delimiter, i.e `>`, `)`, `]`, is missing its start equivalent.
    MissingDelimiterStart(usize),
    /// Too many path elements.
    ///
    /// `TypePathElem` only allows one element.
    TooManyElements,
    /// Zero path elements.
    ///
    /// `TypePathElem` needs one element.
    ZeroElements,
}

/// A result type with an implicit `PathError`.
pub type Result<T> = std::result::Result<T, PathError>;

/// Iterates through a path, counting elements.
///
/// Returns None if this isn't a valid path.
fn path_len(path: &str) -> Result<usize> {
    if path.is_empty() {
        return Ok(0);
    }
    let mut count = 1;
    let mut current_path_delim = PATH_SEPERATOR.chars();
    let mut path_iter = path.char_indices();

    fn end_delim(path_iter: &mut std::str::CharIndices<'_>, end: char, index: usize) -> Result<()> {
        while let Some((i, c)) = path_iter.next() {
            if c == end {
                return Ok(());
            }

            skip_delims(path_iter, c, i)?;
        }

        Err(PathError::MissingDelimiterEnd(index))
    }

    fn skip_delims(
        path_iter: &mut std::str::CharIndices,
        current: char,
        index: usize,
    ) -> Result<()> {
        if let Some((_, end)) = PATH_DELIMS.iter().find(|(start, _)| *start == current) {
            end_delim(path_iter, *end, index)
        } else if PATH_DELIMS.iter().any(|(_, end)| *end == current) {
            Err(PathError::MissingDelimiterStart(index))
        } else {
            Ok(())
        }
    }

    let mut is_empty = true;

    while let Some((i, c)) = path_iter.next() {
        match current_path_delim.next() {
            Some(expected) => {
                if c == expected {
                    continue;
                } else {
                    is_empty = false;
                }
            }
            None => {
                count += 1;
                if PATH_SEPERATOR.starts_with(c) || is_empty {
                    return Err(PathError::EmptyElem(i));
                }
            }
        }
        current_path_delim = PATH_SEPERATOR.chars();
        skip_delims(&mut path_iter, c, i)?;
    }

    if current_path_delim.next().is_none() {
        return Err(PathError::EmptyElem(path.len()));
    }

    Ok(count)
}

impl TypePath {
    /// Insert `other` at the start of `self`.
    pub fn push_start(&mut self, other: TypePath<impl AsRef<str>>) {
        if self.is_empty() {
            self.0.push_str(other.as_str());
        } else if !other.is_empty() {
            self.0.insert_str(0, PATH_SEPERATOR);
            self.0.insert_str(0, other.as_str());
        }
    }

    /// Insert `other` at the end of `self`.
    pub fn push(&mut self, other: TypePath<impl AsRef<str>>) {
        if self.is_empty() {
            self.0.push_str(other.as_str());
        } else if !other.is_empty() {
            self.0.push_str(PATH_SEPERATOR);
            self.0.push_str(other.as_str());
        }
    }

    /// Insert `other` at the end of `self`.
    ///
    /// This fails if `other` is not a valid path.
    pub fn push_str(&mut self, other: &str) -> Result<()> {
        self.push(TypePath::new(other)?);
        Ok(())
    }
}

impl<S: AsRef<str>> AsRef<str> for TypePath<S> {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl<S> TypePath<S> {
    /// Creates a new type path without checking for correctness.
    ///
    /// This isn't unsafe but a lot of logic assumes a `TypePath` to be correct so would
    /// still cause bugs to use this incorrectly.
    pub fn new_unchecked(inner: S) -> Self {
        Self(inner)
    }

    pub fn into_inner(self) -> S {
        self.0
    }

    pub fn get_inner(&self) -> &S {
        &self.0
    }

    /// This isn't unsafe but a lot of logic assumes a `TypePath` to be correct so would
    /// still cause bugs to use this incorrectly.
    pub fn get_inner_mut(&mut self) -> &mut S {
        &mut self.0
    }
}

impl<S: AsRef<str>> TypePath<S> {
    /// Create an empty type path.
    ///
    /// This is equivalent to `TypePath::new_unchecked("".into())`.
    pub fn empty() -> Self
    where
        S: From<&'static str>,
    {
        Self("".into())
    }

    /// Create a new `TypePath` with checks that it is valid.
    pub fn new(s: S) -> Result<Self> {
        path_len(s.as_ref())?;

        Ok(Self(s))
    }

    /// Tries to convert this type path into a type path element.
    ///
    /// Only succeeds if `self.len() == 1`.
    pub fn try_into_elem(self) -> Result<TypePathElem<S>> {
        TypePathElem::try_from(self)
    }

    /// Get the internal string slice of this type path.
    pub fn as_str(&self) -> &str {
        self.0.as_ref()
    }

    /// Borrows this path.
    pub fn borrow(&self) -> TypePath<&str> {
        TypePath(self.as_str())
    }

    /// The amount of segments in a path.
    pub fn len(&self) -> usize {
        path_len(self.as_str()).expect("Invariant")
    }

    /// If the path is empty.
    pub fn is_empty(&self) -> bool {
        self.as_str().is_empty()
    }

    /// The amount of bytes inside of the path.
    pub fn byte_len(&self) -> usize {
        self.as_str().len()
    }

    /// Convert this into an owned type path.
    pub fn to_owned(&self) -> TypePath {
        TypePath(self.as_str().to_string())
    }

    /// Appends `other` to the end of `self`.
    /// If `self` is empty, return `other`.
    /// If `other` is empty, return `self`.
    /// If both are empty, return an empty path.
    pub fn join<T: AsRef<str>>(&self, other: &TypePath<T>) -> TypePath {
        match (self.is_empty(), other.is_empty()) {
            (true, true) => TypePath::empty(),
            (false, true) => self.to_owned(),
            (true, false) => other.to_owned(),
            (false, false) => TypePath(format!("{self}{PATH_SEPERATOR}{other}")),
        }
    }

    /// Split the start segment with the remaining segments.
    pub fn get_start(&self) -> Option<(TypePathElem<&str>, TypePath<&str>)> {
        self.borrow().split_start()
    }

    /// Split the end segment with the remaining segments.
    pub fn get_end(&self) -> Option<(TypePath<&str>, TypePathElem<&str>)> {
        self.borrow().split_end()
    }

    /// Create an iterator for iterating the segments of `self`.
    pub fn iter(&self) -> PathIter {
        PathIter {
            path: self.borrow(),
        }
    }

    /// Check if `self` ends with the path `other`.
    pub fn ends_with(&self, other: TypePath<&str>) -> bool {
        self.as_str().ends_with(other.as_str())
            && (self.byte_len() == other.byte_len()
                || (self.byte_len() - other.byte_len())
                    .checked_sub(PATH_SEPERATOR.len())
                    .is_some_and(|i| &self.as_str()[i..i + PATH_SEPERATOR.len()] == PATH_SEPERATOR))
    }

    /// Check if `self` start with the path `other`.
    pub fn starts_with(&self, other: TypePath<&str>) -> bool {
        self.as_str().starts_with(other.as_str())
            && (self.byte_len() == other.byte_len()
                || self
                    .as_str()
                    .get(other.byte_len()..other.byte_len() + PATH_SEPERATOR.len())
                    == Some(PATH_SEPERATOR))
    }

    /// Returns true if this type path, referencing a type, is something that is
    /// allowed to be parsed by Bauble.
    ///
    /// Certain paths to types may be unparsable to Bauble yet valid internally,
    /// therefore this method is useful to make that distinction. An example of
    /// this are array and tuple types.
    ///
    /// This means that:
    /// - The path is non-empty.
    /// - All the path segments are valid rust identifiers.
    pub fn is_representable_type(&self) -> bool {
        !self.is_empty()
            && self.iter().all(|part| {
                let mut s = part.as_str().chars();

                s.next()
                    .expect("Invariant, path parts aren't empty.")
                    .is_ident_start()
                    && s.all(|c| c.is_ident_continue())
            })
    }

    /// Determines if a path referencing an object is a path to a sub-object.
    /// The path is assumed to be valid.
    ///
    /// This means that:
    /// - The path contains the special '@' sub-object character.
    pub fn is_subobject(&self) -> bool {
        self.iter().any(|part| part.as_str().contains('@'))
    }
}

impl<'a> TypePath<&'a str> {
    /// Returns (root, rest)
    ///
    /// Returns `None` if self is empty
    pub fn split_start(&self) -> Option<(TypePathElem<&'a str>, TypePath<&'a str>)> {
        if self.is_empty() {
            return None;
        }
        let mut split = None;
        let mut current_path_delim = PATH_SEPERATOR.chars();
        let mut path_iter = self.as_str().char_indices();

        // We can assume the path is valid, so no need to check if it actually is.
        fn end_delim(path_iter: &mut std::str::CharIndices<'_>, start: char, end: char) {
            let mut level: u32 = 0;
            for (_, c) in path_iter.by_ref() {
                if c == start {
                    level += 1;
                } else if c == end {
                    if let Some(l) = level.checked_sub(1) {
                        level = l;
                    } else {
                        return;
                    }
                }
            }
        }

        fn skip_delims(path_iter: &mut std::str::CharIndices, current: char) {
            if let Some((start, end)) = PATH_DELIMS.iter().find(|(start, _)| *start == current) {
                end_delim(path_iter, *start, *end);
            }
        }

        while let Some((i, c)) = path_iter.next() {
            match current_path_delim.next() {
                Some(expected) => {
                    if c == expected {
                        continue;
                    }
                }
                None => {
                    split = Some(i);
                    break;
                }
            }

            current_path_delim = PATH_SEPERATOR.chars();
            skip_delims(&mut path_iter, c);
        }

        if let Some(split) = split {
            let root = &self.0[..split - PATH_SEPERATOR.len()];
            let rest = &self.0[split..];

            debug_assert_eq!(
                &self.as_str()[split - PATH_SEPERATOR.len()..split],
                PATH_SEPERATOR
            );

            Some((TypePathElem(TypePath(root)), TypePath(rest)))
        } else {
            Some((TypePathElem(*self), TypePath("")))
        }
    }

    /// Returns (root, elem)
    ///
    /// Returns `None` if self is empty
    pub fn split_end(&self) -> Option<(TypePath<&'a str>, TypePathElem<&'a str>)> {
        if self.is_empty() {
            return None;
        }
        let mut split = None;
        let mut current_path_delim = PATH_SEPERATOR.chars().rev();
        let mut path_iter = self.as_str().char_indices().rev();

        // We can assume the path is valid, so no need to check if it actually is.
        fn end_delim(
            path_iter: &mut std::iter::Rev<std::str::CharIndices<'_>>,
            start: char,
            end: char,
        ) {
            let mut level: u32 = 0;
            for (_, c) in path_iter.by_ref() {
                if c == end {
                    level += 1;
                } else if c == start {
                    if let Some(l) = level.checked_sub(1) {
                        level = l;
                    } else {
                        return;
                    }
                }
            }
        }

        fn skip_delims(path_iter: &mut std::iter::Rev<std::str::CharIndices>, current: char) {
            if let Some((start, end)) = PATH_DELIMS.iter().find(|(_, end)| *end == current) {
                end_delim(path_iter, *start, *end);
            }
        }

        while let Some((i, c)) = path_iter.next() {
            match current_path_delim.next() {
                Some(expected) => {
                    if c == expected {
                        continue;
                    }
                }
                None => {
                    split = Some(i);
                    break;
                }
            }

            current_path_delim = PATH_SEPERATOR.chars().rev();
            skip_delims(&mut path_iter, c);
        }

        if let Some(split) = split {
            let root = &self.0[..=split];
            let elem = &self.0[split + 1 + PATH_SEPERATOR.len()..];
            debug_assert_eq!(
                &self.as_str()[split + 1..split + 1 + PATH_SEPERATOR.len()],
                PATH_SEPERATOR
            );

            Some((TypePath(root), TypePathElem(TypePath(elem))))
        } else {
            Some((TypePath(""), TypePathElem(*self)))
        }
    }
}

/// An iterator of segments in a path.
pub struct PathIter<'a> {
    path: TypePath<&'a str>,
}

impl<'a> Iterator for PathIter<'a> {
    type Item = TypePathElem<&'a str>;

    fn next(&mut self) -> Option<Self::Item> {
        let (item, rest) = self.path.split_start()?;

        self.path = rest;

        Some(item)
    }
}

impl DoubleEndedIterator for PathIter<'_> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let (rest, item) = self.path.split_end()?;

        self.path = rest;

        Some(item)
    }
}

#[test]
fn test_path_seperating() {
    let simple_path = TypePath::new("root::a::b::elem").unwrap();
    #[track_caller]
    fn assert_path_eq(
        path_pair: Option<(impl std::borrow::Borrow<str>, impl std::borrow::Borrow<str>)>,
        eq: (&str, &str),
    ) {
        let p = path_pair.unwrap();
        let path_pair = (p.0.borrow(), p.1.borrow());
        assert_eq!(path_pair, eq);
    }
    assert_path_eq(simple_path.split_start(), ("root", "a::b::elem"));
    assert_path_eq(simple_path.split_end(), ("root::a::b", "elem"));

    let complex_path =
        TypePath::new("root<some::inner::path>::test::elem<other::path(with::path)>").unwrap();
    assert_path_eq(
        complex_path.split_start(),
        (
            "root<some::inner::path>",
            "test::elem<other::path(with::path)>",
        ),
    );
    assert_path_eq(
        complex_path.split_end(),
        (
            "root<some::inner::path>::test",
            "elem<other::path(with::path)>",
        ),
    );

    let error_path = TypePath::new("root(test<)::test::el]em");
    assert!(error_path.is_err());

    let empty_path = TypePath::new("").unwrap();

    assert_eq!(empty_path, TypePath::empty());
    assert!(empty_path.split_start().is_none());
    assert!(empty_path.split_end().is_none());
}
