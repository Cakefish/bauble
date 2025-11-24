#![allow(clippy::type_complexity)]
use bauble::Bauble;
use bauble::BaubleContext;
use bauble::Object;
use bauble::Ref;
use bauble::path::{TypePath, TypePathElem};

#[derive(Bauble, PartialEq, Debug)]
struct Test {
    x: i32,
    y: u32,
}

fn expected_value_fn<T: for<'a> Bauble<'a> + PartialEq + std::fmt::Debug>(
    expected_value: T,
) -> Box<dyn Fn(Object, &BaubleContext)> {
    Box::new(move |object, ctx| {
        let result = T::from_bauble(object.value, &bauble::DefaultAllocator);
        match result {
            Ok(read_value) => assert_eq!(read_value, expected_value),
            Err(error) => {
                let errors = bauble::BaubleErrors::from(error);
                let error_msg = errors.try_to_string(ctx).unwrap();
                panic!("Error converting object to rust value: \n{error_msg}");
            }
        }
    })
}

struct TestFile {
    path: TypePath,
    content: String,
    expected_values: Vec<Box<dyn Fn(Object, &BaubleContext)>>,
}

macro_rules! test_file {
    ($path:expr, $content:expr, $($expected_value:expr),* $(,)?) => {
        TestFile {
            path: TypePath::new(String::from($path)).unwrap(),
            content: String::from($content),
            expected_values: vec![$(expected_value_fn($expected_value)),*],
        }
    };
}

// Test that parsed objects convert into typed values that match the provided test values.
fn compare_objects(objects: Vec<Object>, files: &[&TestFile], ctx: &BaubleContext) {
    let mut objects = objects.into_iter();
    for (index, test_value) in files.iter().flat_map(|f| &f.expected_values).enumerate() {
        let object = objects.next().unwrap_or_else(|| {
            panic!("{} objects found, test expects more", index);
        });
        test_value(object, ctx);
    }

    if objects.next().is_some() {
        panic!("More objects than test expects");
    }
}

fn make_ctx(with_ctx_builder: &dyn Fn(&mut bauble::BaubleContextBuilder)) -> bauble::BaubleContext {
    let mut ctx = bauble::BaubleContextBuilder::new();
    with_ctx_builder(&mut ctx);
    let ctx = ctx.build();
    ctx.type_registry()
        .validate(true)
        .expect("Invalid type registry");
    ctx
}

fn panic_errors(ctx: &bauble::BaubleContext, errors: bauble::BaubleErrors) -> ! {
    panic!("{}", errors.try_to_string(ctx).unwrap());
}

fn test_load(with_ctx_builder: &dyn Fn(&mut bauble::BaubleContextBuilder), files: &[&TestFile]) {
    let mut ctx = make_ctx(with_ctx_builder);

    // Test initial parsing from source
    for file in files {
        ctx.register_file(file.path.borrow(), &file.content);
    }

    let (objects, errors) = ctx.load_all();
    if !errors.is_empty() {
        panic_errors(&ctx, errors);
    }
    compare_objects(objects, files, &ctx);
}

fn test_reload(
    with_ctx_builder: &dyn Fn(&mut bauble::BaubleContextBuilder),
    start: &[&TestFile],
    new: &[&TestFile],
) {
    let mut ctx = make_ctx(with_ctx_builder);

    // Test initial parsing from source
    for file in start {
        ctx.register_file(file.path.borrow(), &file.content);
    }

    let (objects, errors) = ctx.load_all();
    if !errors.is_empty() {
        panic_errors(&ctx, errors);
    }
    compare_objects(objects, start, &ctx);

    // Test reloading with new content and new files that are nested as submodules.
    let (objects, errors) = ctx.reload_paths(new.iter().map(|f| (f.path.borrow(), &f.content)));
    if !errors.is_empty() {
        panic_errors(&ctx, errors);
    }
    compare_objects(objects, new, &ctx);
}

/// Doesn't fail test when some files have errors as long as all expected values are loaded.
///
/// Expects at least one error.
fn test_load_partial(
    with_ctx_builder: &dyn Fn(&mut bauble::BaubleContextBuilder),
    files: &[&TestFile],
) {
    let mut ctx = make_ctx(with_ctx_builder);

    // Test initial parsing from source
    for file in files {
        ctx.register_file(file.path.borrow(), &file.content);
    }

    let (objects, errors) = ctx.load_all();
    if errors.is_empty() {
        panic!("At least one error is expected");
    } else {
        errors.print_errors(&ctx);
    }
    compare_objects(objects, files, &ctx);
}

#[test]
fn new_nested_reload_paths() {
    let a = &test_file!(
        "a",
        r#"test = integration::Test { x: -5, y: 5 }"#,
        Test { x: -5, y: 5 },
    );

    let new_a = &test_file!(
        "a",
        r#"test = integration::Test { x: -15, y: 15 }"#,
        Test { x: -15, y: 15 },
    );
    let new_ab = &test_file!(
        "a::b",
        r#"test = integration::Test { x: -3, y: 3 }"#,
        Test { x: -3, y: 3 },
    );
    let new_abc = &test_file!(
        "a::b::c",
        r#"test = integration::Test { x: -4, y: 1 }"#,
        Test { x: -4, y: 1 },
    );

    let test = |start: &_, new: &_| {
        test_reload(
            &|ctx| {
                ctx.register_type::<Test, _>();
            },
            start,
            new,
        )
    };

    test(&[a], &[new_a]);
    test(&[a], &[a, new_ab]);
    test(&[a], &[new_a, new_ab, new_abc]);
    test(&[a], &[new_a, new_abc, new_ab]);
}

#[test]
#[should_panic = "This identifier was already used"]
fn duplicate_objects() {
    let a = &test_file!(
        "a",
        "test = integration::Test{ x: -5, y: 5 }\n\
        test = integration::Test{ x: -5, y: 4 }",
        Test { x: -5, y: 5 },
    );

    test_load(
        &|ctx| {
            ctx.register_type::<Test, _>();
        },
        &[a],
    );
}

// NOTE: This currently fails because `b::test` isn't allowed by itself but if we add support for
// that we still want this case to fail.
#[test]
#[should_panic = "found ':' expected identifier, or '*'"]
fn duplicate_objects_across_files() {
    let a = &test_file!(
        "a",
        "b::test = integration::Test{ x: -5, y: 5 }",
        Test { x: -5, y: 5 },
    );
    let ab = &test_file!("a::b", "test = integration::Test{ x: -5, y: 5 }",);

    test_load(
        &|ctx| {
            ctx.register_type::<Test, _>();
        },
        &[a, ab],
    );
}

#[test]
fn empty_module() {
    let a = &test_file!(
        "a",
        "use a::empty_module;\n\
         test = integration::Test { x: -5, y: 5 }",
        Test { x: -5, y: 5 },
    );

    let empty_module = &test_file!("a::empty_module", "",);

    test_load(
        &|ctx| {
            ctx.register_type::<Test, _>();
        },
        &[a, empty_module],
    );
}

#[test]
fn default_uses() {
    let a = &test_file!("a", "test = Test { x: -5, y: 5 }", Test { x: -5, y: 5 },);
    let ab = &test_file!("a::b", "test = Test { x: -4, y: 3 }", Test { x: -4, y: 3 },);

    test_load(
        &|ctx| {
            ctx.register_type::<Test, _>();
            ctx.with_default_use(
                TypePathElem::new("Test").unwrap().to_owned(),
                TypePath::new("integration::Test").unwrap().to_owned(),
            );
        },
        &[a, ab],
    );
}

/// Test that successful files are handled correctly when some files fail to parse.
#[test]
fn some_files_fail() {
    let a = &test_file!(
        "a",
        "test = integration::Test { x: -5, y: 5 }",
        Test { x: -5, y: 5 },
    );
    let b = &test_file!("b", "This file fails to parse",);
    let c = &test_file!(
        "c",
        "test = integration::Test { x: -3, y: 3 }",
        Test { x: -3, y: 3 },
    );

    test_load_partial(
        &|ctx| {
            ctx.register_type::<Test, _>();
        },
        &[a, b, c],
    );
}

#[derive(PartialEq, Debug)]
struct TestRef(String);

impl bauble::Bauble<'_> for TestRef {
    fn construct_type(registry: &mut bauble::types::TypeRegistry) -> bauble::types::Type {
        bauble::types::Type {
            meta: bauble::types::TypeMeta {
                path: bauble::path::TypePath::new("integration::TestRef")
                    .unwrap()
                    .to_owned(),
                ..Default::default()
            },
            kind: bauble::types::TypeKind::Ref(
                registry.get_or_register_type::<Test, bauble::DefaultAllocator>(),
            ),
        }
    }

    fn from_bauble(
        val: bauble::Val,
        _allocator: &bauble::DefaultAllocator,
    ) -> std::result::Result<Self, bauble::ToRustError> {
        match val.value.value {
            bauble::Value::Ref(r) => Ok(Self(String::from(r.as_str()))),
            _ => Err(Self::error(
                val.value.span,
                bauble::ToRustErrorKind::WrongType { found: val.ty },
            )),
        }
    }
}

#[test]
fn same_file_references() {
    let a = &test_file!(
        "a",
        "test = integration::Test { x: -5, y: 5 }\n\
         test_ref = $test",
        Test { x: -5, y: 5 },
        TestRef("a::test".into()),
    );

    test_load(
        &|ctx| {
            ctx.register_type::<Test, _>();
            // TODO: TestRef doesn't need to be registered?!
        },
        &[a],
    );
}

#[test]
// TODO: see todo in `register_assets` about registering assets in the correct order.
#[should_panic = "Expected this path to refer to an asset"]
fn same_file_references_reverse() {
    let a = &test_file!(
        "a",
        "test_ref = $test\n\
        test = integration::Test { x: -5, y: 5 }",
        TestRef("a::test".into()),
        Test { x: -5, y: 5 },
    );

    test_load(
        &|ctx| {
            ctx.register_type::<Test, _>();
            // TODO: TestRef doesn't need to be registered?!
        },
        &[a],
    );
}

#[test]
fn same_file_references_reverse_full() {
    let a = &test_file!(
        "a",
        "test_ref = $a::test\n\
        test = integration::Test { x: -5, y: 5 }",
        TestRef("a::test".into()),
        Test { x: -5, y: 5 },
    );

    test_load(
        &|ctx| {
            ctx.register_type::<Test, _>();
        },
        &[a],
    );
}

#[test]
// TODO: see todo in `register_assets` where `add_use` is called.
#[should_panic = "Expected this path to refer to a valid reference"]
fn reference_with_use() {
    let a = &test_file!(
        "a",
        "use b::test;\n\
        test_ref = $test",
        TestRef("b::test".into()),
    );
    let b = &test_file!(
        "b",
        "test = integration::Test { x: -5, y: 5 }",
        Test { x: -5, y: 5 },
    );

    test_load(
        &|ctx| {
            ctx.register_type::<Test, _>();
        },
        &[a, b],
    );
}

#[test]
pub fn ref_implicit_type() {
    bauble::bauble_test!(
        [Test]
        "t = integration::Test{ x: -5, y: 5 }\n\
        r = $t"
        [
            Test { x: -5, y: 5 },
            Ref::<Test>::from_path(TypePath::new_unchecked("test::t").to_owned()),
        ]
    );

    bauble::bauble_test!(
        [Test]
        "r = $test::t\n\
        t = integration::Test{ x: -5, y: 5 }"
        [
            Ref::<Test>::from_path(TypePath::new_unchecked("test::t").to_owned()),
            Test { x: -5, y: 5 },
        ]
    );
}

#[test]
pub fn ref_explicit_type() {
    bauble::bauble_test!(
        [Test]
        "t = integration::Test{ x: -2, y: 2 }\n\
        r: Ref<integration::Test> = $t"
        [
            Test { x: -2, y: 2 },
            Ref::<Test>::from_path(TypePath::new_unchecked("test::t").to_owned()),
        ]
    );

    bauble::bauble_test!(
        [Test]
        "r: Ref<integration::Test> = $test::t\n\
        t = integration::Test{ x: -2, y: 2 }"
        [
            Ref::<Test>::from_path(TypePath::new_unchecked("test::t").to_owned()),
            Test { x: -2, y: 2 },
        ]
    );
}

#[test]
pub fn ref_explicit_type_multiple_files() {
    bauble::bauble_test!(
        [Test]
        [
            "t = integration::Test{ x: -5, y: 5 }",
            "r: Ref<integration::Test> = $test0::t"
        ]
        [
            Test { x: -5, y: 5 },
            Ref::<Test>::from_path(TypePath::new_unchecked("test0::t").to_owned()),
        ]
    );

    bauble::bauble_test!(
        [Test]
        [
            "r: Ref<integration::Test> = $test1::t",
            "t = integration::Test{ x: -5, y: 5 }"
        ]
        [
            Ref::<Test>::from_path(TypePath::new_unchecked("test1::t").to_owned()),
            Test { x: -5, y: 5 },
        ]
    );
}

#[test]
pub fn ref_implicit_type_multiple_files() {
    bauble::bauble_test!(
        [Test]
        [
            "t = integration::Test{ x: -5, y: 5 }",
            "r = $test0::t"
        ]
        [
            Test { x: -5, y: 5 },
            Ref::<Test>::from_path(TypePath::new_unchecked("test0::t").to_owned()),
        ]
    );

    bauble::bauble_test!(
        [Test]
        [
            "r = $test1::t",
            "t = integration::Test{ x: -5, y: 5 }"
        ]
        [
            Ref::<Test>::from_path(TypePath::new_unchecked("test1::t").to_owned()),
            Test { x: -5, y: 5 },
        ]
    );
}

#[test]
#[should_panic = "Expected this path to refer to a type"]
pub fn ref_explicit_type_incorrect() {
    #[derive(Bauble, PartialEq, Eq, Debug)]
    struct Incorrect(u32);

    bauble::bauble_test!(
        [Test, Incorrect]
        "i: Incorrect = Incorrect(0)\n\
        r: Ref<Incorrect> = $test::t\n\
        t = integration::Test{ x: -2, y: 2 }"
        [
            Incorrect(0),
            Ref::<Test>::from_path(TypePath::new_unchecked("test::t").to_owned()),
            Test { x: -2, y: 2 },
        ]
    );
}

#[test]
fn decimal_digits_identifiers() {
    let a = &test_file!(
        "a",
        "2 = integration::Test { x: -5, y: 5 }\n\
         123 = integration::Test { x: -5, y: 5 }\n\
         test_ref2 = $2
         test_ref23 = $123
         ",
        Test { x: -5, y: 5 },
        Test { x: -5, y: 5 },
        TestRef("a::2".into()),
        TestRef("a::123".into()),
    );

    test_load(
        &|ctx| {
            ctx.register_type::<Test, _>();
        },
        &[a],
    );
}

#[derive(PartialEq, Debug)]
struct TestNamespaceFieldIdent {
    x: i32,
    mynamespace_y: u32,
}

impl<'alloc_lifetime> bauble::Bauble<'alloc_lifetime, bauble::DefaultAllocator>
    for TestNamespaceFieldIdent
{
    fn construct_type(registry: &mut bauble::types::TypeRegistry) -> bauble::types::Type {
        let path =
            bauble::path::TypePath::new("integration::TestNamespaceFieldIdent".to_owned()).unwrap();
        let meta = bauble::types::TypeMeta {
            path,
            ..Default::default()
        };

        let x_field = (
            "x",
            bauble::types::FieldType::from(
                registry.get_or_register_type::<i32, bauble::DefaultAllocator>(),
            ),
        );
        let mynamespace_y_field = (
            "mynamespace::y",
            bauble::types::FieldType::from(
                registry.get_or_register_type::<u32, bauble::DefaultAllocator>(),
            ),
        );

        bauble::types::Type {
            meta,
            kind: bauble::types::TypeKind::Struct(bauble::types::Fields::Named(
                bauble::types::NamedFields::empty().with_required([x_field, mynamespace_y_field]),
            )),
        }
    }
    fn from_bauble(
        bauble::Val {
            attributes:
                bauble::Spanned {
                    value: mut _attributes,
                    span: _attributes_span,
                },
            value: bauble::Spanned { span, value },
            ty,
        }: bauble::Val,
        allocator: &bauble::DefaultAllocator,
    ) -> Result<
        <bauble::DefaultAllocator as bauble::BaubleAllocator<'alloc_lifetime>>::Out<Self>,
        bauble::ToRustError,
    > {
        let bauble::Value::Struct(bauble::FieldsKind::Named(mut fields)) = value else {
            Err(Self::error(
                span,
                bauble::ToRustErrorKind::WrongType { found: ty },
            ))?
        };

        let mut take_field = |name: &str| {
            fields.swap_remove(name).ok_or_else(|| {
                Self::error(
                    span,
                    bauble::ToRustErrorKind::MissingField {
                        field: name.to_owned(),
                    },
                )
            })
        };

        let x = bauble::Bauble::from_bauble(take_field("x")?, allocator)
            .and_then(|res| unsafe { bauble::BaubleAllocator::validate(allocator, res) })?;
        let mynamespace_y =
            bauble::Bauble::from_bauble(take_field("mynamespace::y")?, allocator)
                .and_then(|res| unsafe { bauble::BaubleAllocator::validate(allocator, res) })?;
        let this = Self { x, mynamespace_y };
        Ok(unsafe { bauble::BaubleAllocator::wrap(allocator, this) })
    }
}

#[test]
fn two_part_field() {
    let a = &test_file!(
        "a",
        "test = integration::TestNamespaceFieldIdent{ x: -5, mynamespace::y: 5 }",
        TestNamespaceFieldIdent {
            x: -5,
            mynamespace_y: 5
        },
    );

    test_load(
        &|ctx| {
            ctx.register_type::<TestNamespaceFieldIdent, _>();
        },
        &[a],
    );
}

#[test]
fn name_matching_file_is_simplified() {
    let a = &test_file!(
        "a",
        "a = integration::Test { x: -5, y: 5 }
        a_ref = $a", // local and full path are the same here
        Test { x: -5, y: 5 },
        TestRef("a".into()),
    );
    // test non-top-level file
    let ac = &test_file!(
        "a::c",
        "c = integration::Test { x: -5, y: 5 }\n\
        c_ref_local = $c\n\
        c_ref_full = $a::c",
        Test { x: -5, y: 5 },
        TestRef("a::c".into()),
        TestRef("a::c".into()),
    );
    // test refering to them from a separate file
    let b = &test_file!(
        "b",
        "a_ref = $a\n\
         c_ref = $a::c",
        TestRef("a".into()),
        TestRef("a::c".into()),
    );

    test_load(
        &|ctx| {
            ctx.register_type::<Test, _>();
        },
        &[a, ac, b],
    );
}

// TODO: in stage 2, test that only first object can be named `0`.
