use std::{borrow::Cow, fmt::Debug, sync::Arc};

use chumsky::{prelude::*, text::Char};
use indexmap::IndexMap;

use crate::{
    parse::{
        Binding, Ident, Object,
        value::{Attributes, Path, PathEnd, PathTreeEnd, PathTreeNode, Value, Values},
    },
    spanned::{SpanExt, Spanned},
};

type Extra<'a> = extra::Err<Rich<'a, char, crate::Span>>;

#[derive(Clone)]
pub struct ParserSource<'a, A> {
    pub path: &'a str,
    pub ctx: &'a A,
}

impl<'a, A: crate::AssetContext> chumsky::input::Input<'a> for ParserSource<'a, A> {
    type Span = crate::Span;

    type Token = char;

    type MaybeToken = char;

    type Cursor = usize;

    type Cache = (&'a str, Arc<str>);

    fn begin(self) -> (Self::Cursor, Self::Cache) {
        (
            0,
            (
                self.ctx
                    .get_source(self.path)
                    .map(|s| s.text())
                    .unwrap_or(""),
                self.path.into(),
            ),
        )
    }

    fn cursor_location(cursor: &Self::Cursor) -> usize {
        *cursor
    }

    #[inline(always)]
    unsafe fn next_maybe(
        (text, _): &mut Self::Cache,
        cursor: &mut Self::Cursor,
    ) -> Option<Self::MaybeToken> {
        if *cursor < text.len() {
            // SAFETY: `cursor < self.len()` above guarantees cursor is in-bounds
            //         We only ever return cursors that are at a character boundary
            let c = unsafe {
                text.get_unchecked(*cursor..)
                    .chars()
                    .next()
                    .unwrap_unchecked()
            };
            *cursor += c.len_utf8();
            Some(c)
        } else {
            None
        }
    }

    unsafe fn span(
        (_, file): &mut Self::Cache,
        range: std::ops::Range<&Self::Cursor>,
    ) -> Self::Span {
        crate::Span::new(file.clone(), *range.start..*range.end)
    }
}

impl<'a, A: crate::AssetContext> chumsky::input::ValueInput<'a> for ParserSource<'a, A> {
    unsafe fn next(cache: &mut Self::Cache, cursor: &mut Self::Cursor) -> Option<Self::Token> {
        unsafe { Self::next_maybe(cache, cursor) }
    }
}

impl<'a, A: crate::AssetContext> chumsky::input::ExactSizeInput<'a> for ParserSource<'a, A> {
    unsafe fn span_from(
        cache: &mut Self::Cache,
        range: std::ops::RangeFrom<&Self::Cursor>,
    ) -> Self::Span {
        crate::Span::new(cache.1.clone(), *range.start..cache.0.len())
    }
}

impl<'a, A: crate::AssetContext> chumsky::input::SliceInput<'a> for ParserSource<'a, A> {
    type Slice = &'a str;

    fn full_slice(cache: &mut Self::Cache) -> Self::Slice {
        cache.0
    }

    unsafe fn slice(cache: &mut Self::Cache, range: std::ops::Range<&Self::Cursor>) -> Self::Slice {
        unsafe { cache.0.get_unchecked(*range.start..*range.end) }
    }

    unsafe fn slice_from(
        cache: &mut Self::Cache,
        from: std::ops::RangeFrom<&Self::Cursor>,
    ) -> Self::Slice {
        unsafe { cache.0.get_unchecked(*from.start..) }
    }
}

#[derive(Clone)]
pub enum TextExpected<'src> {
    /// Whitespace (for example: spaces, tabs, or newlines).
    Whitespace,
    /// Inline whitespace (for example: spaces or tabs).
    InlineWhitespace,
    /// A newline character or sequence.
    Newline,
    /// A numeric digit within the given radix range.
    ///
    /// For example:
    ///
    /// - `Digit(0..10)` implies any base-10 digit
    /// - `Digit(1..16)` implies any non-zero hexadecimal digit
    Digit(std::ops::Range<u32>),
    /// Part of an identifier, either ASCII or unicode.
    IdentifierPart,
    /// A specific identifier.
    Identifier(&'src str),
}

impl<'a, T> From<TextExpected<'a>> for chumsky::error::RichPattern<'a, T> {
    fn from(value: TextExpected<'a>) -> Self {
        match value {
            TextExpected::Whitespace => Self::Label(Cow::Borrowed("whitespace")),
            TextExpected::InlineWhitespace => Self::Label(Cow::Borrowed("inline whitespace")),
            TextExpected::Newline => Self::Label(Cow::Borrowed("newline")),
            TextExpected::Digit(r) if r.start > 0 => Self::Label(Cow::Borrowed("non-zero digit")),
            TextExpected::Digit(_) => Self::Label(Cow::Borrowed("digit")),
            TextExpected::IdentifierPart => Self::Label(Cow::Borrowed("identifier")),
            TextExpected::Identifier(i) => Self::Identifier(i.to_string()),
        }
    }
}

#[derive(Clone, Copy)]
struct State<T>(T);

impl<'src, T: Copy, I: Input<'src>> chumsky::inspector::Inspector<'src, I> for State<T> {
    type Checkpoint = State<T>;
    #[inline(always)]
    fn on_token(&mut self, _: &<I as Input<'src>>::Token) {}
    #[inline(always)]
    fn on_save<'parse>(&self, _: &chumsky::input::Cursor<'src, 'parse, I>) -> Self::Checkpoint {
        *self
    }
    #[inline(always)]
    fn on_rewind<'parse>(
        &mut self,
        c: &chumsky::input::Checkpoint<'src, 'parse, I, Self::Checkpoint>,
    ) {
        *self = *c.inspector();
    }
}

// TODO Re-add error recovery
pub fn parser<'a, A: crate::AssetContext + 'a>()
-> impl Parser<'a, ParserSource<'a, A>, Values, Extra<'a>> {
    let comment_end = just::<_, ParserSource<'a, A>, Extra<'a>>('\n').or(end().map(|_| '\0'));
    let comments = just("/*")
        .ignore_then(
            recursive(move |more_comment| {
                just("*/")
                    .map_with(|_, e| {
                        let state: &mut State<usize> = e.state();
                        let res: Option<usize> = state.0.checked_sub(1);
                        if let Some(new_state) = res {
                            state.0 = new_state;
                        }
                        res
                    })
                    .filter(|d| d.is_none())
                    .ignored()
                    .or(just("/*")
                        .map_with(|_, e| {
                            let state: &mut State<usize> = e.state();

                            state.0 += 1
                        })
                        .or_not()
                        .then(more_comment.clone())
                        .ignored())
                    .or(any().ignore_then(more_comment).ignored())
            })
            .with_state(State(0usize)),
        )
        .ignored()
        .or(just("//")
            .ignore_then(recursive::<'_, '_, ParserSource<'a, A>, char, _, _, _>(
                |more_comment| comment_end.or(any().ignore_then(more_comment)),
            ))
            .ignored())
        .padded()
        .repeated()
        .padded(); // Have to pad again in case there are no repetitions

    // A rust identifier, use snake case.
    let ident = any()
        .try_map(|c: char, span| {
            if c.is_ident_start() {
                Ok(c)
            } else {
                Err(
                    chumsky::label::LabelError::<ParserSource<'a, A>, _>::expected_found(
                        [TextExpected::IdentifierPart],
                        Some(chumsky::util::MaybeRef::Val(c)),
                        span,
                    ),
                )
            }
        })
        .then(
            any()
                .try_map(|c: char, span| {
                    if c.is_ident_continue() {
                        Ok(c)
                    } else {
                        Err(
                            chumsky::label::LabelError::<ParserSource<'a, A>, _>::expected_found(
                                [TextExpected::IdentifierPart],
                                Some(chumsky::util::MaybeRef::Val(c)),
                                span,
                            ),
                        )
                    }
                })
                .repeated(),
        )
        .to_slice()
        .map_with(|ident: &str, e| ident.to_owned().spanned(e.span()));

    let path_start = ident.then_ignore(just("::")).repeated().collect::<Vec<_>>();
    let path_end = ident
        .map(PathEnd::Ident)
        .or(just("*::").ignore_then(ident).map(PathEnd::WithIdent));
    let path = path_start
        .map_with(|v, e| v.spanned(e.span()))
        .then(path_end.map_with(|v, e| v.spanned(e.span())))
        .map(|(leading, last)| Path { leading, last });

    let uses = just("use")
        .padded_by(comments.clone())
        .ignore_then(recursive::<
            '_,
            '_,
            ParserSource<'a, A>,
            Spanned<PathTreeNode>,
            _,
            _,
            _,
        >(|node| {
            let path_end = path_end.map(PathTreeEnd::PathEnd);
            let everything = just('*').map(|_| PathTreeEnd::Everything);

            let group = node
                .padded_by(comments.clone())
                .separated_by(just(',').padded_by(comments.clone()))
                .allow_trailing()
                .collect()
                .delimited_by(
                    just('{').padded_by(comments.clone()),
                    just('}').padded_by(comments.clone()),
                )
                .map(PathTreeEnd::Group);
            path_start
                .map_with(|v, e| v.spanned(e.span()))
                .then(
                    path_end
                        .or(everything)
                        .or(group)
                        .map_with(|end, e| end.spanned(e.span())),
                )
                .map_with(|(start, end), e| {
                    PathTreeNode {
                        leading: start,
                        end,
                    }
                    .spanned(e.span())
                })
        }))
        .then_ignore(just(';').padded_by(comments.clone()))
        .repeated()
        .collect();

    let object = recursive(
        |object: Recursive<dyn Parser<'a, ParserSource<'a, A>, Object, Extra<'a>>>| {
            let attribute = just('#').ignore_then(
                ident
                    .padded()
                    .padded_by(comments.clone())
                    .then_ignore(just('='))
                    .then(object.clone())
                    .separated_by(just(','))
                    .allow_trailing()
                    .collect()
                    .delimited_by(just('['), just(']')),
            );

            let attributes = attribute
                .padded_by(comments.clone())
                .repeated()
                .collect()
                .map_with(|value: Vec<Vec<(Ident, Object)>>, e| {
                    value
                        .into_iter()
                        .flatten()
                        .collect::<IndexMap<_, _>>()
                        .spanned(e.span())
                })
                .map(|attributes| Attributes(attributes.value).spanned(attributes.span))
                .boxed();

            let int = any()
                .try_map(move |c: char, span| {
                    if c.is_ascii_digit() && c != char::digit_zero() {
                        Ok(c)
                    } else {
                        Err(
                            chumsky::label::LabelError::<ParserSource<'a, A>, _>::expected_found(
                                [TextExpected::Digit(1..10)],
                                Some(chumsky::util::MaybeRef::Val(c)),
                                span,
                            ),
                        )
                    }
                })
                .then(
                    any()
                        .try_map(move |c: char, span| {
                            if c.is_ascii_digit() {
                                Ok(())
                            } else {
                                Err(chumsky::label::LabelError::<ParserSource<'a, A>, _>::expected_found(
                                    [TextExpected::Digit(0..10)],
                                    Some(chumsky::util::MaybeRef::Val(c)),
                                    span,
                                ))
                            }
                        })
                        .repeated(),
                )
                .ignored()
                .or(just(char::digit_zero()).ignored())
                .to_slice();

            let digits = any()
                .try_map(move |c: char, span| {
                    if c.is_ascii_digit() {
                        Ok(c)
                    } else {
                        Err(
                            chumsky::label::LabelError::<ParserSource<'a, A>, _>::expected_found(
                                [TextExpected::Digit(0..10)],
                                Some(chumsky::util::MaybeRef::Val(c)),
                                span,
                            ),
                        )
                    }
                })
                .repeated()
                .at_least(1);

            // A number with or without decimals.
            let num = just('-')
                .or_not()
                .then(int)
                .then(just('.').ignore_then(digits.to_slice()).or_not())
                .to_slice()
                .try_map(|s: &str, span| {
                    Ok(Value::Num(s.parse().map_err(|_| {
                        Rich::custom(span, "Failed to parse number")
                    })?))
                });

            // A parser for strings, with escape characters
            let escape = just('\\').ignore_then(
                just('\\')
                    .or(just('/'))
                    .or(just('"'))
                    .or(just('b').to('\x08'))
                    .or(just('f').to('\x0C'))
                    .or(just('n').to('\n'))
                    .or(just('r').to('\r'))
                    .or(just('t').to('\t'))
                    .or(just('u').ignore_then(
                        any()
                            .filter(char::is_ascii_hexdigit)
                            .repeated()
                            .exactly(4)
                            .collect::<String>()
                            .validate(|digits, e, emit| {
                                char::from_u32(u32::from_str_radix(&digits, 16).unwrap())
                                    .unwrap_or_else(|| {
                                        emit.emit(Rich::custom(
                                            e.span(),
                                            "Invalid unicode character",
                                        ));
                                        '\u{FFFD}' // unicode replacement character
                                    })
                            }),
                    )),
            );
            let string = just('"')
                .ignore_then(none_of("\\\"").or(escape).repeated().collect::<String>())
                .then_ignore(just('"'))
                .map(Value::Str);

            let literal = just('#').ignore_then(
                select! {
                    c if c.is_alphanumeric() => (),
                    '!' | '#' | '@' | '%' | '&' | '?' | '.' | '=' | '<' | '>' | '_' | '-' | '+' | '*' | '/' | '\\' => (),
                }
                    .repeated()
                    .to_slice()
                    .map(str::to_string)
                    .map(Value::Raw),
            );

            // Parser for bools
            let bool_ = just("true")
                .map(|_| Value::Bool(true))
                .or(just("false").map(|_| Value::Bool(false)));

            let separator = just(',').padded_by(comments.clone());

            let sequence = object
                .clone()
                .separated_by(separator.clone())
                .allow_trailing()
                .collect::<Vec<_>>()
                .padded();

            // Parser for arrays.
            let array = sequence
                .clone()
                .delimited_by(
                    just('[').padded_by(comments.clone()),
                    just(']').padded_by(comments.clone()),
                )
                .map(Value::Array);

            let tuple = sequence
                .delimited_by(
                    just('(').padded_by(comments.clone()),
                    just(')').padded_by(comments.clone()),
                )
                .recover_with(via_parser(nested_delimiters(
                    '(',
                    ')',
                    [('{', '}'), ('[', ']')],
                    |_| Vec::new(),
                )));

            let structure = ident
                .padded_by(comments.clone())
                .padded()
                .then_ignore(just(':').padded().padded_by(comments.clone()))
                .then(object.clone())
                .separated_by(separator.clone())
                .allow_trailing()
                .collect::<Vec<_>>()
                .padded()
                .delimited_by(
                    just('{').padded_by(comments.clone()),
                    just('}').padded_by(comments.clone()),
                )
                .map(|fields| fields.into_iter().collect())
                .recover_with(via_parser(nested_delimiters(
                    '{',
                    '}',
                    [('[', ']'), ('(', ')')],
                    |_| crate::parse::Fields::new(),
                )));

            let reference = just('$').ignore_then(path).map_with(|path, e| {
                // We have at least 1 element in the path.
                Value::Ref(path.spanned(e.span()))
            });

            let path_p = path
                .map_with(|path, e| path.spanned(e.span()))
                .padded_by(comments.clone())
                .padded();

            // Parser for tuple structs
            let named_tuple =
                path_p
                    .clone()
                    .then(tuple.clone())
                    .map(|(name, fields)| Value::Tuple {
                        name: Some(name),
                        fields,
                    });

            // Parser for Structs
            let named_struct = path_p
                .clone()
                .then(structure.clone())
                .map(|(name, fields)| Value::Struct {
                    name: Some(name),
                    fields,
                });

            // Parser for a structure, without an identifier
            let map = object
                .clone()
                .padded_by(comments.clone())
                .then_ignore(just(':'))
                .then(object.padded_by(comments.clone()))
                .separated_by(separator)
                .allow_trailing()
                .collect::<Vec<_>>()
                .padded()
                .delimited_by(
                    just('{').padded_by(comments.clone()),
                    just('}').padded_by(comments.clone()),
                )
                .recover_with(via_parser(nested_delimiters(
                    '{',
                    '}',
                    [('[', ']'), ('(', ')')],
                    |_| Vec::new(),
                )))
                .map(Value::Map);

            // Parser for a tuple.
            let tuple = tuple.map(|fields| Value::Tuple { name: None, fields });

            let path_or = path_p
                .separated_by(just('|').padded_by(comments.clone()))
                .at_least(2)
                .collect()
                .map(Value::Or);

            let path = path.map_with(|path, e| Value::Path(path.spanned(e.span())));

            // The start of a raw string: count the number of open braces
            let start_raw = just('{').repeated().at_least(1).count();
            // The end of a raw string: accept only *exactly* as many close braces as that which opened it
            let end_raw = just('}')
                .repeated()
                .configure(|repeat, ctx| repeat.exactly(*ctx));
            // A raw string is then just any character that's *not* the start of the end
            let raw = just('#')
                .ignore_then(
                    start_raw.ignore_with_ctx(
                        any()
                            .and_is(end_raw.not())
                            .repeated()
                            .to_slice()
                            .then_ignore(end_raw),
                    ),
                )
                .map(str::to_string)
                .map(Value::Raw);

            let value = choice((
                bool_,
                num,
                string,
                reference,
                array,
                tuple,
                map,
                named_tuple,
                named_struct,
                path_or,
                path,
                raw,
                literal,
            ))
            // TODO Get this recovery method working again
            //
            .recover_with(skip_then_retry_until(
                any().ignored(),
                one_of(['}', ']', ')']).ignored(),
            ));

            attributes
                .then(
                    value
                        .map_with(|value, e| value.spanned(e.span()))
                        .padded_by(comments.clone())
                        .padded()
                        .boxed(),
                )
                .map(|(attributes, value)| Object { attributes, value })
        },
    );

    fn binding<'a, V: 'a + Debug, A: crate::AssetContext + 'a>(
        ident: impl 'a + Parser<'a, ParserSource<'a, A>, Ident, Extra<'a>>,
        value: impl 'a + Parser<'a, ParserSource<'a, A>, V, Extra<'a>>,
        path: impl 'a + Parser<'a, ParserSource<'a, A>, Spanned<Path>, Extra<'a>> + Clone,
        comments: impl 'a + Clone + Parser<'a, ParserSource<'a, A>, (), Extra<'a>>,
    ) -> impl Parser<'a, ParserSource<'a, A>, (Ident, Option<Spanned<Path>>, V), Extra<'a>> {
        ident
            .padded_by(comments.clone())
            .padded()
            .then(
                just(':')
                    .padded_by(comments.clone())
                    .padded()
                    .ignore_then(path)
                    .padded_by(comments.clone())
                    .padded()
                    .or_not(),
            )
            .then_ignore(just('=').padded().padded_by(comments))
            .then(value)
            .map(|((ident, ty), val)| (ident, ty, val))
            .boxed()
    }

    enum ItemType {
        Value,
        Copy,
    }

    let path = path.map_with(|p, e| p.spanned(e.span()));

    uses.then(
        just("copy")
            .padded()
            .ignore_then(binding(ident, object.clone(), path, comments.clone()))
            .map(|binding| (binding, ItemType::Copy))
            .or(binding(ident, object, path, comments).map(|binding| (binding, ItemType::Value)))
            .repeated()
            .collect::<Vec<_>>(),
    )
    .map(|(uses, values)| {
        values.into_iter().fold(
            Values {
                uses,
                values: IndexMap::default(),
                copies: IndexMap::default(),
            },
            |mut values, ((ident, type_path, object), ty)| {
                match ty {
                    ItemType::Value => {
                        values.values.insert(ident, Binding { type_path, object });
                    }
                    ItemType::Copy => {
                        values.copies.insert(ident, object);
                    }
                }
                values
            },
        )
    })
    .then_ignore(end())
}
