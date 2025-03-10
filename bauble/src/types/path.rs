use std::ops::Deref;

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

impl<S: AsRef<str>> std::fmt::Debug for TypePathElem<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(self.as_str(), f)
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
    pub fn new(s: S) -> Result<Self> {
        let l = path_len(s.as_ref())?;
        match l {
            0 => Err(PathError::ZeroElements),
            1 => Ok(Self(TypePath(s))),
            2.. => Err(PathError::TooManyElements),
        }
    }

    pub fn to_owned(&self) -> TypePathElem<String> {
        TypePathElem(self.0.to_owned())
    }

    pub fn borrow(&self) -> TypePathElem<&str> {
        TypePathElem(self.0.borrow())
    }

    pub fn is_empty(&self) -> bool {
        false
    }

    pub fn len(&self) -> usize {
        1
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

impl<S: AsRef<str>> std::fmt::Debug for TypePath<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(self.as_str(), f)
    }
}

impl<S: AsRef<str>> std::fmt::Display for TypePath<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.as_str(), f)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PathError {
    EmptyElem(usize),
    MissingEnd(usize),
    MissingStart(usize),
    TooManyElements,
    ZeroElements,
}

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

        Err(PathError::MissingEnd(index))
    }

    fn skip_delims(
        path_iter: &mut std::str::CharIndices,
        current: char,
        index: usize,
    ) -> Result<()> {
        if let Some((_, end)) = PATH_DELIMS.iter().find(|(start, _)| *start == current) {
            end_delim(path_iter, *end, index)
        } else if PATH_DELIMS.iter().any(|(_, end)| *end == current) {
            Err(PathError::MissingStart(index))
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
                is_empty = true;
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
    pub fn push_start(&mut self, other: TypePath<impl AsRef<str>>) {
        if self.is_empty() {
            self.0.push_str(other.as_str());
        } else if !other.is_empty() {
            self.0.insert_str(0, PATH_SEPERATOR);
            self.0.insert_str(0, other.as_str());
        }
    }

    pub fn push(&mut self, other: TypePath<impl AsRef<str>>) {
        if self.is_empty() {
            self.0.push_str(other.as_str());
        } else if !other.is_empty() {
            self.0.push_str(PATH_SEPERATOR);
            self.0.push_str(other.as_str());
        }
    }

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

impl<S: AsRef<str>> TypePath<S> {
    pub fn empty() -> Self
    where
        S: From<&'static str>,
    {
        Self("".into())
    }

    pub fn new(s: S) -> Result<Self> {
        path_len(s.as_ref())?;

        Ok(Self(s))
    }

    pub fn try_into_elem(self) -> Result<TypePathElem<S>> {
        TypePathElem::try_from(self)
    }

    pub fn as_str(&self) -> &str {
        self.0.as_ref()
    }

    pub fn borrow(&self) -> TypePath<&str> {
        TypePath(self.as_str())
    }

    pub fn len(&self) -> usize {
        path_len(self.as_str()).expect("Invariant")
    }

    pub fn is_empty(&self) -> bool {
        self.as_str().is_empty()
    }

    pub fn byte_len(&self) -> usize {
        self.as_str().len()
    }

    pub fn to_owned(&self) -> TypePath {
        TypePath(self.as_str().to_string())
    }

    pub fn combine<T: AsRef<str>>(&self, other: &TypePath<T>) -> TypePath {
        match (self.is_empty(), other.is_empty()) {
            (true, true) => TypePath::empty(),
            (true, false) => self.to_owned(),
            (false, true) => other.to_owned(),
            (false, false) => TypePath(format!("{self}{PATH_SEPERATOR}{other}")),
        }
    }

    /// Returns (root, rest)
    ///
    /// Returns `None` if self is empty
    pub fn split_start(&self) -> Option<(TypePathElem<&str>, TypePath<&str>)> {
        if self.is_empty() {
            return None;
        }
        let mut split = self.byte_len();
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
                    split = i;
                    break;
                }
            }

            current_path_delim = PATH_SEPERATOR.chars();
            skip_delims(&mut path_iter, c);
        }

        let root = &self.as_str()[..split - PATH_SEPERATOR.len()];
        let rest = &self.as_str()[split..];

        debug_assert_eq!(
            &self.as_str()[split - PATH_SEPERATOR.len()..split],
            PATH_SEPERATOR
        );

        Some((TypePathElem(TypePath(root)), TypePath(rest)))
    }

    /// Returns (root, elem)
    ///
    /// Returns `None` if self is empty
    pub fn split_end(&self) -> Option<(TypePath<&str>, TypePathElem<&str>)> {
        if self.is_empty() {
            return None;
        }
        let mut split = 0;
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
                    split = i;
                    break;
                }
            }

            current_path_delim = PATH_SEPERATOR.chars().rev();
            skip_delims(&mut path_iter, c);
        }

        let root = &self.as_str()[..=split];
        let elem = &self.as_str()[split + 1 + PATH_SEPERATOR.len()..];
        debug_assert_eq!(
            &self.as_str()[split + 1..split + 1 + PATH_SEPERATOR.len()],
            PATH_SEPERATOR
        );

        Some((TypePath(root), TypePathElem(TypePath(elem))))
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
