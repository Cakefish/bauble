#![feature(iterator_try_collect, let_chains, ptr_metadata)]

pub mod bauble_trait;
pub mod context;
pub mod error;
pub mod parse;
pub mod spanned;
pub mod types;
pub mod value;

pub use bauble_macros::Bauble;

pub use bauble_trait::{
    Bauble, BaubleAllocator, DefaultAllocator, ToRustError, ToRustErrorKind, VariantKind,
};
pub use context::{BaubleContext, FileId, Source};
pub use error::{BaubleError, BaubleErrors, print_errors};
pub use spanned::{Span, SpanExt, Spanned};
pub use types::path;
pub use value::{Attributes, ConversionError, FieldsKind, Object, Val, Value};

#[doc(hidden)]
pub mod private {
    pub use indexmap::IndexMap;
}

use parse::Values;

pub fn parse(file_id: FileId, ctx: &BaubleContext) -> Result<Values, BaubleErrors> {
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

pub fn convert(file_id: FileId, ctx: &BaubleContext) -> Result<Vec<Object>, BaubleErrors> {
    let values = parse(file_id, ctx)?;

    value::convert_values(file_id, values, &value::Symbols::new(ctx))
}
