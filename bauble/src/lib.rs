#![feature(
    iterator_try_reduce,
    array_try_map,
    iterator_try_collect,
    arbitrary_self_types,
    pattern
)]
mod convert;
pub mod parse;
pub mod spanned;
pub mod value;

pub use bauble_macros::FromBauble;

pub use chumsky::span::SimpleSpan;
pub use convert::{BaubleAllocator, DefaultAllocator, DeserializeError, FromBauble, VariantKind};
pub use spanned::{SpanExt, Spanned};
pub use value::{
    convert_values, AssetContext, Attributes, ConvertionError, FieldsKind, Object, TypeInfo, Val,
    Value, ValueKind,
};

use parse::Values;
fn parse(src: &str) -> Option<Values> {
    use ariadne::{Color, Label, Report, ReportKind, Source};
    use chumsky::Parser;

    let parser = parse::parser().then_ignore(chumsky::primitive::end());
    let result = parser.parse(src);

    result.errors().for_each(|e| {
        Report::build(ReportKind::Error, (), e.span().start)
            .with_code(3)
            .with_message(e.to_string())
            .with_label(
                Label::new(e.span().into_range())
                    .with_message(e.reason().to_string())
                    .with_color(Color::Red),
            )
            .finish()
            .eprint(Source::from(&src))
            .unwrap();
    });

    result.into_output()
}

pub fn simple_convert(src: &str) -> Result<Vec<Object>, Spanned<ConvertionError>> {
    let values =
        parse(src).ok_or(ConvertionError::ParseError.span(SimpleSpan::new(0, src.len())))?;

    let ctx = value::NoChecks;

    convert_values("".to_string(), values, &value::Symbols::new(&ctx))
}
