#![feature(iterator_try_collect, let_chains, ptr_metadata)]

mod context;
mod error;
mod parse;
mod spanned;
mod traits;
mod value;

pub mod types;

pub use bauble_macros::Bauble;

pub use context::{BaubleContext, BaubleContextBuilder, FileId, Source};
pub use error::{BaubleError, BaubleErrors, CustomError, print_errors};
pub use spanned::{Span, SpanExt, Spanned};
pub use traits::{
    Bauble, BaubleAllocator, DefaultAllocator, ToRustError, ToRustErrorKind, VariantKind,
};
pub use types::path;
pub use value::{Attributes, ConversionError, FieldsKind, Object, PrimitiveValue, Val, Value};

#[doc(hidden)]
pub mod private {
    pub use indexmap::IndexMap;
}

use parse::Values;

fn parse(file_id: FileId, ctx: &BaubleContext) -> Result<Values, BaubleErrors> {
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

#[macro_export]
macro_rules! bauble_test {
    ([$($ty:ty),* $(,)?] $source:literal [$($expr:expr),* $(,)?]) => {
        {
            let mut ctx = $crate::BaubleContextBuilder::new();
            $(ctx.register_type::<$ty, _>();)*
            let mut ctx = ctx.build();
            ctx.register_file($crate::path::TypePath::new("test").unwrap(), format!("\n{}\n", $source));

            let (objects, errors) = ctx.load_all();

            if !errors.is_empty() {
                $crate::print_errors(Err::<(), _>(errors), &ctx);

                panic!("Error converting");
            }

            let mut objects = objects.into_iter();
            $(
                let value = objects.next().expect("Not as many objects as test expr in bauble test?");
                let mut read_value = $expr;
                let test_value = ::std::mem::replace(&mut read_value, $crate::print_errors(Bauble::from_bauble(value.value, &::bauble::DefaultAllocator), &ctx).unwrap());


                assert_eq!(
                    read_value,
                    test_value,
                );
            )*
        }
    };
}
