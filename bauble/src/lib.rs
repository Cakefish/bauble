//! Bauble is Rust-inspired human-readable text format for representing various Rust-like data, such as enums or structs.
//!
//! Data represented by Bauble can be parsed and stored in memory in the form of a corresponding type on Rust which implements
//! the [`Bauble`] trait. In this way, Bauble is a format very useful for specifying information processed to Rust in a way
//! that remains very consistent to the actual Rust code itself that makes use of the information.
//!
//! The code making use of Bauble has to construct a [`BaubleContext`] in order to provide the parsing step enough information
//! for recognizing the different types inside of the Bauble source. Once a context has been created, that context can then be
//! used for parsing various Bauble source files and extract the newly parsed data back as typed values that can be used to
//! update the state of the program.
//!
//! # BaubleContext
//!
//! [`BaubleContext`] is used to register various Bauble source files to parse information from, as well as maintaining a type
//! registry where every known type to Bauble is provided. All interactions with Bauble require a context.
//!
//! # Deriving Bauble
//!
//! In order to represent a type inside of Bauble, you must implement the `Bauble` trait for that type. To make this easier,
//! Bauble has a custom derive macro `#[derive(Bauble)]`.
//!
//! Here is a following example of using `#[derive(Bauble)]` to create a Bauble parsable type.
//! ```
//! # use bauble::Bauble;
//!
//! #[derive(Bauble)]
//! struct TypeInBauble {
//!    a_number: u32,
//!    a_string: String,
//!    a_bool: bool,
//! }
//! ```
//!
//! More information on the [`Bauble`] derive macro exists in its documentation.

#![feature(iterator_try_collect, let_chains, ptr_metadata)]
#![warn(missing_docs)]

mod context;
mod error;
mod parse;
mod spanned;
mod traits;
mod value;

pub mod types;

pub use bauble_macros::Bauble;

pub use context::{BaubleContext, BaubleContextBuilder, FileId, PathReference, Source};
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

// re-exporting crates from other crates
pub use rust_decimal as decimal;

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

// TODO(@docs)
#[allow(missing_docs)]
#[macro_export]
macro_rules! bauble_test {
    ( [$($ty:ty),* $(,)?] $source:literal [$($expr:expr),* $(,)?]) => {
        $crate::bauble_test!(__TEST_CTX [$($ty),*] $source [$($expr),*])
    };
    ($ctx_static:ident [$($ty:ty),* $(,)?] $source:literal [$($expr:expr),* $(,)?]) => {
        static $ctx_static: std::sync::OnceLock<std::sync::RwLock<$crate::BaubleContext>> = std::sync::OnceLock::new();
        {
            let file_path = $crate::path::TypePath::new("test").unwrap();
            let ctx = $ctx_static.get_or_init(|| {
                let mut ctx = $crate::BaubleContextBuilder::new();
                $(ctx.register_type::<$ty, _>();)*

                let mut ctx = ctx.build();
                ctx.type_registry().validate(true).expect("Invalid type registry");

                ctx.register_file(file_path, format!("\n{}\n", $source));

                std::sync::RwLock::new(ctx)
            });

            let (objects, errors) = ctx.write().unwrap().load_all();

            if !errors.is_empty() {
                $crate::print_errors(Err::<(), _>(errors), &ctx.read().unwrap());

                panic!("Error converting");
            }

            let re_source = $crate::display_formatted(objects.as_slice(), ctx.read().unwrap().type_registry(), &$crate::DisplayConfig {
                ..$crate::DisplayConfig::default()
            });

            let (re_objects, errors) = ctx.write().unwrap().reload_paths([(file_path, re_source.as_str())]);

            if !errors.is_empty() {
                $crate::print_errors(Err::<(), _>(errors), &ctx.read().unwrap());

                println!("{re_source}");

                panic!("Error re-converting");
            }

            let compare_objects = |mut objects: Vec<$crate::Object>| {
                let mut objects = objects.into_iter();

                $(
                    let value = objects.next().expect("Not as many objects as test expr in bauble test?");
                    let mut read_value = $expr;
                    let test_value = ::std::mem::replace(&mut read_value, $crate::print_errors(Bauble::from_bauble(value.value, &::bauble::DefaultAllocator), &ctx.read().unwrap()).unwrap());


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
