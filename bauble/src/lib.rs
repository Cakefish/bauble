#![feature(iterator_try_collect)]

pub mod convert;
pub mod parse;
pub mod spanned;
pub mod value;

pub use bauble_macros::FromBauble;

pub use convert::{BaubleAllocator, DefaultAllocator, DeserializeError, FromBauble, VariantKind};
use spanned::Span;
pub use spanned::{SpanExt, Spanned};
use value::AssetContextCache;
pub use value::{
    AssetContext, Attributes, ConversionError, FieldsKind, Object, OwnedTypeInfo, Source, TypeInfo,
    Val, Value, ValueKind, convert_values,
};

use parse::Values;

pub fn parse(path: &str, ctx: &impl AssetContext) -> Option<Values> {
    use ariadne::{Color, Label, Report, ReportKind};
    use chumsky::Parser;

    let parser = parse::parser();
    let result = parser.parse(parse::ParserSource { path, ctx });

    result.errors().for_each(|e| {
        Report::build(ReportKind::Error, e.span().clone())
            .with_message(e.to_string())
            .with_label(
                Label::new(e.span().clone())
                    .with_message(e.reason().to_string())
                    .with_color(Color::Red),
            )
            .finish()
            .eprint(AssetContextCache(ctx))
            .unwrap();
    });

    result.into_output()
}

pub fn convert(path: &str, ctx: impl AssetContext) -> Option<Vec<Object>> {
    let values = parse(path, &ctx)?;

    convert_values(path, values, &value::Symbols::new(&ctx))
}
