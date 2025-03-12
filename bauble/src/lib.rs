#![feature(iterator_try_collect, let_chains, ptr_metadata)]

pub mod bauble_context;
pub mod convert;
pub mod error;
pub mod parse;
pub mod spanned;
pub mod types;
pub mod value;

pub use bauble_macros::Bauble;

pub use bauble_context::{AssetContext, FileId};
pub use convert::{
    Bauble, BaubleAllocator, DefaultAllocator, DeserializeError, FromBaubleError,
    FullDeserializeError, VariantKind,
};
pub use error::{BaubleError, BaubleErrors, print_errors};
pub use spanned::{Span, SpanExt, Spanned};
pub use types::path;
pub use value::{Attributes, ConversionError, FieldsKind, Object, Val, Value, convert_values};

pub mod private {
    pub use indexmap::IndexMap;
}

use parse::Values;

pub fn parse(file_id: FileId, ctx: &impl AssetContext) -> Result<Values, BaubleErrors> {
    use chumsky::Parser;

    let parser = parse::parser();
    let result = parser.parse(parse::ParserSource { file_id, ctx });

    result.into_result().map_err(|errors| {
        BaubleErrors::from(
            errors
                .into_iter()
                .map(|e| e.into_owned())
                .collect::<Vec<_>>(),
        )
    })
}

pub fn convert(file_id: FileId, ctx: &impl AssetContext) -> Result<Vec<Object>, BaubleErrors> {
    let values = parse(file_id, ctx)?;

    convert_values(file_id, values, &value::Symbols::new(ctx))
}
