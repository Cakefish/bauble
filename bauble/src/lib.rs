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
pub use error::{BaubleError, BaubleErrors, CustomError, Level, print_errors};
pub use spanned::{Span, SpanExt, Spanned};
pub use traits::{
    Bauble, BaubleAllocator, DefaultAllocator, ToRustError, ToRustErrorKind, VariantKind,
};
pub use types::path;
pub use value::{
    Attributes, ConversionError, DisplayConfig, Fields, FieldsKind, IndentedDisplay, Map, Object,
    PrimitiveValue, Sequence, SpannedValue, UnspannedVal, Val, Value, ValueContainer, ValueTrait,
    display_formatted,
};

#[doc(hidden)]
pub mod private {
    pub use indexmap::IndexMap;
}

use parse::ParseValues;

fn parse(file_id: FileId, ctx: &BaubleContext) -> Result<ParseValues, BaubleErrors> {
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
            ctx.type_registry().validate(true).expect("Invalid type registry");
            let file_path = $crate::path::TypePath::new("test").unwrap();
            ctx.register_file(file_path, format!("\n{}\n", $source));

            let (objects, errors) = ctx.load_all();

            if !errors.is_empty() {
                $crate::print_errors(Err::<(), _>(errors), &ctx);

                panic!("Error converting");
            }

            let re_source = $crate::display_formatted(objects.as_slice(), ctx.type_registry(), &$crate::DisplayConfig {
                ..$crate::DisplayConfig::default()
            });

            let (re_objects, errors) = ctx.reload_paths([(file_path, re_source.as_str())]);

            if !errors.is_empty() {
                $crate::print_errors(Err::<(), _>(errors), &ctx);

                println!("{re_source}");

                panic!("Error re-converting");
            }

            let compare_objects = |mut objects: Vec<$crate::Object>| {
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
            };

            assert_eq!(objects, re_objects);

            compare_objects(objects);
            compare_objects(re_objects);
        }
    };
}
