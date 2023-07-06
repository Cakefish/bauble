#![feature(iterator_try_collect)]

pub mod convert;
pub mod parse;
pub mod spanned;
pub mod value;

pub use bauble_macros::FromBauble;

pub use chumsky::span::SimpleSpan;
pub use convert::{BaubleAllocator, DefaultAllocator, DeserializeError, FromBauble, VariantKind};
pub use spanned::{SpanExt, Spanned};
pub use value::{
    convert_values, AssetContext, Attributes, ConversionError, FieldsKind, Object, OwnedTypeInfo,
    TypeInfo, Val, Value, ValueKind,
};

use parse::Values;
fn parse(src: &str) -> Option<Values> {
    use ariadne::{Color, Label, Report, ReportKind, Source};
    use chumsky::Parser;

    let parser = parse::parser();
    let result = parser.parse(src);

    result.errors().for_each(|e| {
        Report::build(ReportKind::Error, (), e.span().start)
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

/// Converts a source with no checks.
pub fn simple_convert(src: &str) -> Result<Vec<Object>, Spanned<ConversionError>> {
    let values =
        parse(src).ok_or(ConversionError::ParseError.span(SimpleSpan::new(0, src.len())))?;

    let ctx = value::NoChecks;

    convert_values("".to_string(), values, &value::Symbols::new(&ctx))
}

pub fn convert(
    src: &str,
    file_name: impl Into<String>,
    ctx: &impl AssetContext,
) -> Result<Vec<Object>, Spanned<ConversionError>> {
    let values =
        parse(src).ok_or(ConversionError::ParseError.span(SimpleSpan::new(0, src.len())))?;

    convert_values(file_name.into(), values, &value::Symbols::new(&ctx))
}
