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
pub use context::{AssetKind, BaubleContext, BaubleContextBuilder, FileId, PathReference, Source};
pub use error::{BaubleError, BaubleErrors, CustomError, Level};
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

    use crate::path::TypePath;
    use std::sync::{OnceLock, RwLock};

    pub fn bauble_test_impl(
        ctx: &OnceLock<RwLock<crate::BaubleContext>>,
        file_sources: &[&str],
        register_types: &dyn Fn(&mut crate::BaubleContextBuilder),
        compare_objects: &dyn Fn(Vec<crate::Object>, &RwLock<crate::BaubleContext>),
    ) {
        let file_paths = if file_sources.len() == 1 {
            vec![TypePath::new(String::from("test")).unwrap()]
        } else {
            (0..file_sources.len())
                .map(|i| TypePath::new(format!("test{i}")).unwrap())
                .collect()
        };

        let ctx = ctx.get_or_init(|| {
            let mut ctx = crate::BaubleContextBuilder::new();
            register_types(&mut ctx);

            let mut ctx = ctx.build();
            ctx.type_registry()
                .validate(true)
                .expect("Invalid type registry");

            for (path, source) in file_paths.iter().zip(file_sources) {
                ctx.register_file(path.borrow(), format!("\n{}\n", source));
            }

            RwLock::new(ctx)
        });

        // Test initial parsing from source
        let (objects, errors) = ctx.write().unwrap().load_all();

        if !errors.is_empty() {
            let error_msg = errors.try_to_string(&ctx.read().unwrap()).unwrap();
            panic!("Error converting: \n{error_msg}");
        }

        // Test round-trip of objects through source format
        let mut file_objects = std::collections::HashMap::new();
        for object in &objects {
            use crate::SpannedValue;
            file_objects
                .entry(object.value.span().file())
                .or_insert(Vec::new())
                .push(object.clone());
        }

        let re_path_sources = file_objects
            .iter()
            .map(|(file_id, objects)| {
                let ctx = ctx.read().unwrap();
                let re_source = crate::display_formatted(
                    objects.as_slice(),
                    ctx.type_registry(),
                    &crate::DisplayConfig {
                        ..crate::DisplayConfig::default()
                    },
                );
                (ctx.get_file_path(*file_id).to_owned(), re_source)
            })
            .collect::<Vec<_>>();

        let (re_objects, errors) = ctx
            .write()
            .unwrap()
            .reload_paths(re_path_sources.iter().map(|(p, s)| (p.borrow(), s)));

        if !errors.is_empty() {
            let mut error_msg = errors.try_to_string(&ctx.read().unwrap()).unwrap();
            for (path, re_source) in re_path_sources {
                use std::fmt::Write;
                writeln!(&mut error_msg, "In file \"{path}\":\n{re_source}").unwrap();
            }
            panic!("Error re-converting: \n{error_msg}");
        }

        assert_eq!(objects, re_objects);

        // Test that original parsed objects and round-trip objects convert into typed values
        // that match the provided test values.
        compare_objects(objects, ctx);
        compare_objects(re_objects, ctx);
    }

    /// Converts bauble object to the type of the `expected_value` and then asserts that they are
    /// the same.
    ///
    /// Panics if converting object fails.
    pub fn expected_from_bauble<T>(
        expected_value: T,
        value: crate::Object,
        ctx: &std::sync::RwLock<crate::BaubleContext>,
    ) where
        T: PartialEq + for<'a> crate::Bauble<'a> + std::fmt::Debug,
    {
        match <T as crate::Bauble>::from_bauble(value.value, &crate::DefaultAllocator) {
            Ok(read_value) => {
                assert_eq!(read_value, expected_value);
            }
            Err(error) => {
                let error_msg = crate::BaubleErrors::from(error)
                    .try_to_string(&ctx.read().unwrap())
                    .unwrap();
                panic!("Error converting object to rust value: \n{error_msg}");
            }
        }
    }
}

// TODO(@docs)
#[allow(missing_docs)]
#[macro_export]
macro_rules! bauble_test {
    ( [$($ty:ty),* $(,)?] $source:literal [$($test_value:expr),* $(,)?]) => {
        { $crate::bauble_test!(__TEST_CTX [$($ty),*] [$source] [$($test_value),*]); }
    };
    ( [$($ty:ty),* $(,)?] [$($source:literal),* $(,)?] [$($test_value:expr),* $(,)?]) => {
        { $crate::bauble_test!(__TEST_CTX [$($ty),*] [$($source),*] [$($test_value),*]); }
    };
    ($ctx_static:ident [$($ty:ty),* $(,)?] [$($source:literal),* $(,)?] [$($test_value:expr),* $(,)?]) => {
        static $ctx_static: std::sync::OnceLock<std::sync::RwLock<$crate::BaubleContext>> = std::sync::OnceLock::new();
        {
            let file_sources = [$($source),*];

            let register_types = |ctx: &mut $crate::BaubleContextBuilder| {
                $(ctx.register_type::<$ty, _>();)*
            };

            let compare_objects = |mut objects: Vec<$crate::Object>, ctx: &std::sync::RwLock<$crate::BaubleContext>| {
                let mut objects = objects.into_iter();

                $(
                    let value = objects.next().expect("Not as many objects as test expr in bauble test?");
                    $crate::private::expected_from_bauble($test_value, value, &ctx);
                )*

                if objects.next().is_some() {
                    panic!("More objects in bauble test than test expr?");
                }
            };

            $crate::private::bauble_test_impl(
                &$ctx_static,
                &file_sources,
                &register_types,
                &compare_objects,
            )
        }
    };
}
