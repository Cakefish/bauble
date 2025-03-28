use std::{borrow::Cow, fmt::Debug};

use chumsky::{prelude::*, text::Char};
use indexmap::IndexMap;

use crate::{
    Attributes, BaubleContext, FieldsKind, PrimitiveValue, Value,
    context::FileId,
    parse::{
        Binding, ParseVal,
        value::{Path, PathEnd, PathTreeEnd, PathTreeNode, Values},
    },
    spanned::{SpanExt, Spanned},
    value::Ident,
};

type Extra<'a> = extra::Err<Rich<'a, char, crate::Span>>;

#[derive(Clone)]
pub struct ParserSource<'a> {
    pub file_id: FileId,
    pub ctx: &'a BaubleContext,
}

impl<'a> chumsky::input::Input<'a> for ParserSource<'a> {
    type Span = crate::Span;

    type Token = char;

    type MaybeToken = char;

    type Cursor = usize;

    type Cache = (&'a str, FileId);

    fn begin(self) -> (Self::Cursor, Self::Cache) {
        let (cursor, cache) = <&'a str as Input>::begin(self.ctx.get_source(self.file_id).text());

        (cursor, (cache, self.file_id))
    }

    fn cursor_location(cursor: &Self::Cursor) -> usize {
        *cursor
    }

    #[inline(always)]
    unsafe fn next_maybe(
        (text, _): &mut Self::Cache,
        cursor: &mut Self::Cursor,
    ) -> Option<Self::MaybeToken> {
        // SAFETY: Requirements passed to caller since we used `<&str as Input>::begin` in our
        // `begin` function.
        unsafe { <&'a str as Input>::next_maybe(text, cursor) }
    }

    unsafe fn span(
        (_, file): &mut Self::Cache,
        range: std::ops::Range<&Self::Cursor>,
    ) -> Self::Span {
        crate::Span::new(*file, *range.start..*range.end)
    }
}

impl<'a> chumsky::input::ValueInput<'a> for ParserSource<'a> {
    unsafe fn next(cache: &mut Self::Cache, cursor: &mut Self::Cursor) -> Option<Self::Token> {
        // SAFETY: Requirements passed to caller since we used `<&str as Input>::begin` in our
        // `begin` function.
        unsafe { Self::next_maybe(cache, cursor) }
    }
}

impl<'a> chumsky::input::ExactSizeInput<'a> for ParserSource<'a> {
    unsafe fn span_from(
        cache: &mut Self::Cache,
        range: std::ops::RangeFrom<&Self::Cursor>,
    ) -> Self::Span {
        crate::Span::new(cache.1, *range.start..cache.0.len())
    }
}

impl<'a> chumsky::input::SliceInput<'a> for ParserSource<'a> {
    type Slice = &'a str;

    fn full_slice(cache: &mut Self::Cache) -> Self::Slice {
        cache.0
    }

    unsafe fn slice(
        (text, _): &mut Self::Cache,
        range: std::ops::Range<&Self::Cursor>,
    ) -> Self::Slice {
        // SAFETY: Requirements passed to caller since we used `<&str as Input>::begin` in our
        // `begin` function.
        unsafe { <&'a str as chumsky::input::SliceInput<'a>>::slice(text, range) }
    }

    unsafe fn slice_from(
        (text, _): &mut Self::Cache,
        from: std::ops::RangeFrom<&Self::Cursor>,
    ) -> Self::Slice {
        // SAFETY: Requirements passed to caller since we used `<&str as Input>::begin` in our
        // `begin` function.
        unsafe { <&'a str as chumsky::input::SliceInput<'a>>::slice_from(text, from) }
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
pub fn parser<'a>() -> impl Parser<'a, ParserSource<'a>, Values, Extra<'a>> {
    let comment_end = just::<_, ParserSource<'a>, Extra<'a>>('\n').or(end().map(|_| '\0'));
    let comments = just("//")
        .ignore_then(recursive::<'_, '_, ParserSource<'a>, char, _, _, _>(
            |more_comment| comment_end.or(any().ignore_then(more_comment)),
        ))
        .ignored()
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
                    chumsky::label::LabelError::<ParserSource<'a>, _>::expected_found(
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
                            chumsky::label::LabelError::<ParserSource<'a>, _>::expected_found(
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
            ParserSource<'a>,
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
        |object: Recursive<dyn Parser<'a, ParserSource<'a>, ParseVal, Extra<'a>>>| {
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
                .map_with(|value: Vec<Vec<(Ident, ParseVal)>>, e| {
                    value
                        .into_iter()
                        .flatten()
                        .collect::<IndexMap<_, _>>()
                        .spanned(e.span())
                })
                .map(|attributes| Attributes::from(attributes.value).spanned(attributes.span))
                .boxed();

            let int = any()
                .try_map(move |c: char, span| {
                    if c.is_ascii_digit() && c != char::digit_zero() {
                        Ok(c)
                    } else {
                        Err(
                            chumsky::label::LabelError::<ParserSource<'a>, _>::expected_found(
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
                                Err(chumsky::label::LabelError::<ParserSource<'a>, _>::expected_found(
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
                            chumsky::label::LabelError::<ParserSource<'a>, _>::expected_found(
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
                    Ok(Value::Primitive(PrimitiveValue::Num(s.parse().map_err(
                        |_| Rich::custom(span, "Failed to parse number"),
                    )?)))
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
                .map(|v| Value::Primitive(PrimitiveValue::Str(v)));

            let literal = just('#').ignore_then(
                select! {
                    c if c.is_alphanumeric() => (),
                    '!' | '#' | '@' | '%' | '&' | '?' | '.' | '=' | '<' | '>' | '_' | '-' | '+' | '*' | '/' | '\\' => (),
                }
                    .repeated()
                    .to_slice()
                    .map(str::to_string)
                    .map(|v| Value::Primitive(PrimitiveValue::Raw(v))),
            );

            // Parser for bools
            let bool_ = just("true")
                .map(|_| Value::Primitive(PrimitiveValue::Bool(true)))
                .or(just("false").map(|_| Value::Primitive(PrimitiveValue::Bool(false))));

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

            let reference = just('$').ignore_then(path).map(|path| {
                // We have at least 1 element in the path.
                Value::Ref(path)
            });

            let path_p = path.padded_by(comments.clone()).padded();

            // Parser for tuple structs
            let unnamed_struct = path_p
                .clone()
                .then(tuple.clone())
                .map(|(name, fields)| (Some(name), Value::Struct(FieldsKind::Unnamed(fields))));

            // Parser for structs
            let named_struct = path_p
                .clone()
                .then(structure.clone())
                .map(|(name, fields)| (Some(name), Value::Struct(FieldsKind::Named(fields))));

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
            let tuple = tuple.map(Value::Tuple);

            let path_or = path_p
                .map_with(|path, e| path.spanned(e.span()))
                .separated_by(just('|').padded_by(comments.clone()))
                .at_least(2)
                .collect()
                .map(Value::Or);

            let path = path.map(|path: Path| (Some(path), Value::Struct(FieldsKind::Unit)));

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
                .map(|v| Value::Primitive(PrimitiveValue::Raw(v)));

            let no_type = |t| (None, t);
            let value = choice((
                bool_.map(no_type),
                num.map(no_type),
                string.map(no_type),
                reference.map(no_type),
                array.map(no_type),
                tuple.map(no_type),
                map.map(no_type),
                unnamed_struct,
                named_struct,
                path_or.map(no_type),
                path,
                raw.map(no_type),
                literal.map(no_type),
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
                .map(
                    #[expect(clippy::type_complexity)]
                    |(attributes, spanned): (
                        _,
                        Spanned<(Option<Path>, crate::Value<ParseVal, Path, Path>)>,
                    )| {
                        let Spanned {
                            span,
                            value: (ty, value),
                        } = spanned;
                        ParseVal {
                            ty,
                            attributes,
                            value: value.spanned(span),
                        }
                    },
                )
        },
    );

    fn binding<'a, V: 'a + Debug>(
        ident: impl 'a + Parser<'a, ParserSource<'a>, Ident, Extra<'a>>,
        value: impl 'a + Parser<'a, ParserSource<'a>, V, Extra<'a>>,
        path: impl 'a + Parser<'a, ParserSource<'a>, Path, Extra<'a>> + Clone,
        comments: impl 'a + Clone + Parser<'a, ParserSource<'a>, (), Extra<'a>>,
    ) -> impl Parser<'a, ParserSource<'a>, (Ident, Option<Path>, V), Extra<'a>> {
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
            |mut values, ((ident, type_path, value), ty)| {
                let binding = Binding { type_path, value };
                match ty {
                    ItemType::Value => {
                        values.values.insert(ident, binding);
                    }
                    ItemType::Copy => {
                        values.copies.insert(ident, binding);
                    }
                }
                values
            },
        )
    })
    .then_ignore(end())
}
