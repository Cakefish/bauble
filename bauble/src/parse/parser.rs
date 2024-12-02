use std::fmt::Debug;

use chumsky::prelude::*;
use indexmap::IndexMap;

use crate::{
    parse::{
        value::{Attributes, Path, PathEnd, PathTreeEnd, PathTreeNode, Value, Values},
        Binding, Ident, Object,
    },
    spanned::{SpanExt, Spanned},
};

type Error<'a> = extra::Err<Rich<'a, char>>;
// TODO Re-add error recovery
pub fn parser<'a>() -> impl Parser<'a, &'a str, Values, Error<'a>> {
    let comment_end = just('\n').or(end().map(|_| '\0'));
    let comments = just("//")
        .ignore_then(recursive::<'_, '_, &str, char, _, _, _>(|more_comment| {
            comment_end.or(any().ignore_then(more_comment))
        }))
        .ignored()
        .padded()
        .repeated()
        .padded(); // Have to pad again in case there are no repetitions

    // A rust identifier, use snake case.
    let ident = text::ident()
        .map_with(|ident: &str, e| ident.to_owned().spanned(e.span()))
        .padded();

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
        .ignore_then(recursive::<'_, '_, &str, Spanned<PathTreeNode>, _, _, _>(
            |node| {
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
            },
        ))
        .then_ignore(just(';').padded_by(comments.clone()))
        .repeated()
        .collect();

    let object = recursive(
        |object: Recursive<dyn Parser<'a, &'a str, Object, Error<'a>>>| {
            let attribute = just('#').ignore_then(
                ident
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

            // A number with or without decimals.
            let num = just('-')
                .or_not()
                .then(text::int(10))
                .then(just('.').ignore_then(text::digits(10).to_slice()).or_not())
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

            let tuple = sequence.delimited_by(
                just('(').padded_by(comments.clone()),
                just(')').padded_by(comments.clone()),
            );

            let structure = ident
                .padded_by(comments.clone())
                .padded()
                .then_ignore(just(':'))
                .then(object.clone())
                .separated_by(separator.clone())
                .allow_trailing()
                .collect::<Vec<_>>()
                .padded()
                .delimited_by(
                    just('{').padded_by(comments.clone()),
                    just('}').padded_by(comments.clone()),
                )
                .map(|fields| fields.into_iter().collect());

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
            .recover_with(via_parser(nested_delimiters(
                '{',
                '}',
                [('[', ']'), ('(', ')')],
                |_| Value::Error,
            )))
            .recover_with(via_parser(nested_delimiters(
                '[',
                ']',
                [('{', '}'), ('(', ')')],
                |_| Value::Error,
            )))
            .recover_with(via_parser(nested_delimiters(
                '(',
                ')',
                [('{', '}'), ('[', ']')],
                |_| Value::Error,
            )));
            // TODO Get this recovery method working again
            //
            // .recover_with(skip_then_retry_until(
            //     any().ignored(),
            //     one_of(['}', ']', ')']),
            // ));

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

    fn binding<'a, V: 'a + Debug>(
        ident: impl 'a + Parser<'a, &'a str, Ident, extra::Err<Rich<'a, char>>>,
        value: impl 'a + Parser<'a, &'a str, V, extra::Err<Rich<'a, char>>>,
        path: impl 'a + Parser<'a, &'a str, Spanned<Path>, extra::Err<Rich<'a, char>>> + Clone,
        comments: impl 'a + Clone + Parser<'a, &'a str, (), extra::Err<Rich<'a, char>>>,
    ) -> impl Parser<'a, &'a str, (Ident, Option<Spanned<Path>>, V), extra::Err<Rich<'a, char>>>
    {
        ident
            .padded_by(comments.clone())
            .padded()
            .then(
                just(':')
                    .ignore_then(path)
                    .padded_by(comments)
                    .padded()
                    .or_not(),
            )
            .then_ignore(just('='))
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
