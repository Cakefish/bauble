#![doc = include_str!("../../OVERVIEW.md")]
#![feature(iterator_try_collect, let_chains, ptr_metadata)]
#![warn(missing_docs)]

mod builtin;
mod context;
mod error;
mod parse;
mod spanned;
mod traits;
mod value;

pub mod types;

pub use bauble_macros::Bauble;

pub use builtin::Ref;
pub use context::{BaubleContext, BaubleContextBuilder, FileId, PathReference, Source};
pub use error::{BaubleError, BaubleErrors, CustomError, Level, print_errors};
pub use spanned::{Span, SpanExt, Spanned};
pub use traits::{
    Bauble, BaubleAllocator, DefaultAllocator, ToRustError, ToRustErrorKind, VariantKind,
};
pub use types::path;
pub use value::{
    AdditionalUnspannedObjects, Attributes, CompareObjectsError, ConversionError, DisplayConfig,
    Fields, FieldsKind, IndentedDisplay, Map, Object, PrimitiveValue, Sequence, SpannedValue,
    UnspannedVal, Val, Value, ValueContainer, ValueTrait, compare_object_sets, display_formatted,
};

// re-exporting crates from other crates
pub use rust_decimal as decimal;

#[doc(hidden)]
pub mod private {
    pub use indexmap::IndexMap;
}

// TODO(@docs)
#[allow(missing_docs)]
#[macro_export]
macro_rules! bauble_test {
    ( [$($ty:ty),* $(,)?] $source:literal [$($test_value:expr),* $(,)?]) => {
        $crate::bauble_test!(__TEST_CTX [$($ty),*] [$source] [$($test_value),*])
    };
    ( [$($ty:ty),* $(,)?] [$($source:literal),* $(,)?] [$($test_value:expr),* $(,)?]) => {
        $crate::bauble_test!(__TEST_CTX [$($ty),*] [$($source),*] [$($test_value),*])
    };
    ($ctx_static:ident [$($ty:ty),* $(,)?] [$($source:literal),* $(,)?] [$($test_value:expr),* $(,)?]) => {{
        static $ctx_static: std::sync::OnceLock<std::sync::RwLock<$crate::BaubleContext>> = std::sync::OnceLock::new();
        {
            let file_path = $crate::path::TypePath::new("test").unwrap();
            let ctx = $ctx_static.get_or_init(|| {
                let mut ctx = $crate::BaubleContextBuilder::new();
                $(ctx.register_type::<$ty, _>();)*

                let mut ctx = ctx.build();
                ctx.type_registry().validate(true).expect("Invalid type registry");

                $(
                    ctx.register_file(file_path, format!("\n{}\n", $source));
                )*

                std::sync::RwLock::new(ctx)
            });

            // Test initial parsing from source
            let (objects, errors) = ctx.write().unwrap().load_all();

            if !errors.is_empty() {
                $crate::print_errors(Err::<(), _>(errors), &ctx.read().unwrap());
                panic!("Error converting");
            }

            // Test round-trip of objects through source format
            let re_source = $crate::display_formatted(objects.as_slice(), ctx.read().unwrap().type_registry(), &$crate::DisplayConfig {
                ..$crate::DisplayConfig::default()
            });

            let (re_objects, errors) = ctx.write().unwrap().reload_paths([(file_path, re_source.as_str())]);

            if !errors.is_empty() {
                $crate::print_errors(Err::<(), _>(errors), &ctx.read().unwrap());
                eprintln!("{re_source}");
                panic!("Error re-converting");
            }

            assert_eq!(objects, re_objects);

            // Test that original parsed objects and round-trip objects convert into typed values
            // that match the provided test values.
            let compare_objects = |mut objects: Vec<$crate::Object>| {
                let mut objects = objects.into_iter();

                $(
                    let value = objects.next().expect("Not as many objects as test expr in bauble test?");
                    // Infer type for `read_value` to be the same as `test_value`.
                    let [test_value, read_value] = [
                        $test_value,
                        $crate::print_errors(
                            $crate::Bauble::from_bauble(value.value, &$crate::DefaultAllocator),
                            &ctx.read().unwrap()
                        ).unwrap(),
                    ];

                    assert_eq!(read_value, test_value);
                )*

                if objects.next().is_some() {
                    panic!("More objects in bauble test than test expr?");
                }
            };

            compare_objects(objects);
            compare_objects(re_objects);
        }
    }};
}
