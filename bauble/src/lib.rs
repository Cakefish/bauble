#![feature(iterator_try_collect, let_chains)]

pub mod convert;
pub mod error;
pub mod parse;
pub mod spanned;
pub mod value;

pub use bauble_macros::FromBauble;

pub use convert::{
    BaubleAllocator, DefaultAllocator, DeserializeError, FromBauble, FromBaubleError, VariantKind,
};
pub use error::{BaubleError, BaubleErrors, print_errors};
pub use spanned::{Span, SpanExt, Spanned};
pub use value::{
    AssetContext, Attributes, ConversionError, FieldsKind, Object, OwnedTypeInfo, Source, TypeInfo,
    Val, Value, ValueKind, convert_values,
};

use parse::Values;

pub fn parse<'a>(path: &'a str, ctx: &'a impl AssetContext) -> Result<Values, BaubleErrors<'a>> {
    use chumsky::Parser;

    let parser = parse::parser();
    let result = parser.parse(parse::ParserSource { path, ctx });

    result.into_result().map_err(BaubleErrors::from)
}

pub fn convert<'a>(
    path: &'a str,
    ctx: &'a impl AssetContext,
) -> Result<Vec<Object>, BaubleErrors<'a>> {
    let values = parse(path, ctx)?;

    convert_values(path, values, &value::Symbols::new(ctx))
}
