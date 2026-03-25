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

impl TestFile {
    fn new(
        path: &str,
        content: &str,
        expected_values: Vec<Box<dyn Fn(Object, &BaubleContext)>>,
    ) -> Self {
        Self {
            path: TypePath::new(String::from(path)).unwrap(),
            content: String::from(content),
            expected_values,
        }
    }
}

macro_rules! test_file {
    ($path:expr, $content:expr, $($expected_value:expr),* $(,)?) => {
        TestFile::new(
            $path,
            $content,
            vec![$(expected_value_fn($expected_value)),*],
        )
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
        r#"0 = integration::Test { x: -5, y: 5 }"#,
        Test { x: -5, y: 5 },
    );

    let new_a = &test_file!(
        "a",
        r#"0 = integration::Test { x: -15, y: 15 }"#,
        Test { x: -15, y: 15 },
    );
    let new_ab = &test_file!(
        "a::b",
        r#"0 = integration::Test { x: -3, y: 3 }"#,
        Test { x: -3, y: 3 },
    );
    let new_abc = &test_file!(
        "a::b::c",
        r#"0 = integration::Test { x: -4, y: 1 }"#,
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
        "0 = integration::Test{ x: -5, y: 5 }\n\
        a = integration::Test{ x: -5, y: 4 }\n\
        a = integration::Test{ x: -5, y: 4 }",
        Test { x: -5, y: 5 },
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
    let ab = &test_file!("a::b", "0 = integration::Test{ x: -5, y: 5 }",);

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
         0 = integration::Test { x: -5, y: 5 }",
        Test { x: -5, y: 5 },
    );

    let empty_module = &test_file!("a::empty_module", "",);

    test_load(
        &|ctx| {
            ctx.register_type::<Test, _>();
        },
        &[a, empty_module],
    );
    test_load(
        &|ctx| {
            ctx.register_type::<Test, _>();
        },
        &[empty_module, a],
    );
}

#[test]
fn default_uses() {
    let a = &test_file!("a", "0 = Test { x: -5, y: 5 }", Test { x: -5, y: 5 },);
    let ab = &test_file!("a::b", "0 = Test { x: -4, y: 3 }", Test { x: -4, y: 3 },);

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
        "0 = integration::Test { x: -5, y: 5 }",
        Test { x: -5, y: 5 },
    );
    let b = &test_file!("b", "This file fails to parse",);
    let c = &test_file!(
        "c",
        "0 = integration::Test { x: -3, y: 3 }",
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
        "0 = integration::Test { x: -5, y: 5 }\n\
         test_ref = $0",
        Test { x: -5, y: 5 },
        TestRef("a".into()),
    );

    test_load(
        &|ctx| {
            ctx.register_type::<Test, _>();
            // NOTE: TestRef doesn't need to be registered?!
        },
        &[a],
    );
}

#[test]
fn same_file_references_reverse() {
    let a = &test_file!(
        "a",
        "0 = $test\n\
        test = integration::Test { x: -5, y: 5 }",
        TestRef("a::test".into()),
        Test { x: -5, y: 5 },
    );

    test_load(
        &|ctx| {
            ctx.register_type::<Test, _>();
            // NOTE: TestRef doesn't need to be registered?!
        },
        &[a],
    );
}

#[test]
fn same_file_references_reverse_full() {
    let a = &test_file!(
        "a",
        "0 = $a::test\n\
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
fn reference_with_use() {
    let a = &test_file!(
        "a",
        "use b::test;\n\
        0 = $test",
        TestRef("b::test".into()),
    );
    let b = &test_file!(
        "b::test",
        "0 = integration::Test { x: -5, y: 5 }",
        Test { x: -5, y: 5 },
    );

    test_load(
        &|ctx| {
            ctx.register_type::<Test, _>();
        },
        // Test when the referencing file is loaded before the referenced file
        &[a, b],
    );
}

#[test]
pub fn ref_implicit_type() {
    bauble::bauble_test!(
        [Test]
        "0 = integration::Test{ x: -5, y: 5 }\n\
        r = $0"
        [
            Test { x: -5, y: 5 },
            Ref::<Test>::from_path(TypePath::new_unchecked("test").to_owned()),
        ]
    );

    bauble::bauble_test!(
        [Test]
        "0 = $test::t\n\
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
        "use integration::Test;\n\
        0 = integration::Test{ x: -2, y: 2 }\n\
        r1: Ref<integration::Test> = $0\n\
        r2: Ref<Test> = $0"
        [
            Test { x: -2, y: 2 },
            Ref::<Test>::from_path(TypePath::new_unchecked("test").to_owned()),
            Ref::<Test>::from_path(TypePath::new_unchecked("test").to_owned()),
        ]
    );

    bauble::bauble_test!(
        [Test]
        "use integration::Test;\n\
        0: Ref<integration::Test> = $test::t\n\
        r2: Ref<Test> = $test::t\n\
        t = integration::Test{ x: -2, y: 2 }"
        [
            Ref::<Test>::from_path(TypePath::new_unchecked("test::t").to_owned()),
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
            "0 = integration::Test{ x: -5, y: 5 }",
            "0: Ref<integration::Test> = $test0"
        ]
        [
            Test { x: -5, y: 5 },
            Ref::<Test>::from_path(TypePath::new_unchecked("test0").to_owned()),
        ]
    );

    bauble::bauble_test!(
        [Test]
        [
            "0: Ref<integration::Test> = $test1",
            "0 = integration::Test{ x: -5, y: 5 }"
        ]
        [
            Ref::<Test>::from_path(TypePath::new_unchecked("test1").to_owned()),
            Test { x: -5, y: 5 },
        ]
    );
}

#[test]
pub fn ref_implicit_type_multiple_files() {
    bauble::bauble_test!(
        [Test]
        [
            "0 = integration::Test{ x: -5, y: 5 }",
            "0 = $test0"
        ]
        [
            Test { x: -5, y: 5 },
            Ref::<Test>::from_path(TypePath::new_unchecked("test0").to_owned()),
        ]
    );

    bauble::bauble_test!(
        [Test]
        [
            "0 = $test1",
            "0 = integration::Test{ x: -5, y: 5 }"
        ]
        [
            Ref::<Test>::from_path(TypePath::new_unchecked("test1").to_owned()),
            Test { x: -5, y: 5 },
        ]
    );
}

#[test]
#[should_panic = "Expected `Ref<integration::Incorrect>` which is a reference to `integration::Incorrect`, which is a struct with unnamed fields, but got `Ref<integration::Test>` which is a reference to `integration::Test`, which is a struct with named fields"]
pub fn ref_explicit_type_incorrect() {
    #[derive(Bauble, PartialEq, Eq, Debug)]
    struct Incorrect(u32);

    bauble::bauble_test!(
        [Test, Incorrect]
        "0: integration::Incorrect = Incorrect(0)\n\
        r: Ref<integration::Incorrect> = $test::t\n\
        t = integration::Test{ x: -2, y: 2 }"
        [
            Incorrect(0),
            Ref::<Test>::from_path(TypePath::new_unchecked("test::t").to_owned()),
            Test { x: -2, y: 2 },
        ]
    );
}

#[test]
#[should_panic = "Expected this path to refer to a type"]
pub fn ref_explicit_type_incorrect_multiple_files() {
    #[derive(Bauble, PartialEq, Eq, Debug)]
    struct Incorrect(u32);

    bauble::bauble_test!(
        [Test, Incorrect]
        [
            "0 = integration::Test{ x: -5, y: 5 }",
            "0: Ref<integration::Incorrect> = $test0"
        ]
        [
            Test { x: -5, y: 5 },
            Ref::<Test>::from_path(TypePath::new_unchecked("test0").to_owned()),
        ]
    );
}

/// Like above, but with file load order reversed.
#[test]
#[should_panic = "Error converting: \n\u{1b}[31mError:\u{1b}[0m Invalid explicit reference path 'Ref<integration::Incorrect>"]
pub fn ref_explicit_type_incorrect_multiple_files_reverse() {
    #[derive(Bauble, PartialEq, Eq, Debug)]
    struct Incorrect(u32);

    bauble::bauble_test!(
        [Test, Incorrect]
        [
            "0: Ref<integration::Incorrect> = $test1",
            "0 = integration::Test{ x: -5, y: 5 }",
        ]
        [
            Ref::<Test>::from_path(TypePath::new_unchecked("test1").to_owned()),
            Test { x: -5, y: 5 },
        ]
    );
}

#[test]
#[should_panic = "Expected `Ref<integration::Incorrect>` which is a reference to `integration::Incorrect`, which is a struct with unnamed fields, but got `Ref<integration::Test>` which is a reference to `integration::Test`, which is a struct with named fields"]
pub fn ref_explicit_type_incorrect_multiple_files_ref_already_registered() {
    #[derive(Bauble, PartialEq, Eq, Debug)]
    struct Incorrect(u32);

    bauble::bauble_test!(
        [Test, Incorrect]
        [
            "0 = integration::Test{ x: -5, y: 5 }",
            "0 = integration::Incorrect(345)",
            "0: Ref<integration::Incorrect> = $test0"
        ]
        [
            Test { x: -5, y: 5 },
            Ref::<Test>::from_path(TypePath::new_unchecked("test0").to_owned()),
        ]
    );
}

#[test]
fn decimal_digits_identifiers() {
    let a = &test_file!(
        "a",
        "0 = integration::Test { x: -5, y: 5 }\n\
         2 = integration::Test { x: -5, y: 5 }\n\
         123 = integration::Test { x: -5, y: 5 }\n\
         test_ref1 = $0
         test_ref2 = $2
         test_ref3 = $123
         ",
        Test { x: -5, y: 5 },
        Test { x: -5, y: 5 },
        Test { x: -5, y: 5 },
        TestRef("a".into()),
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
        "0 = integration::TestNamespaceFieldIdent{ x: -5, mynamespace::y: 5 }",
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
    let a = &TestFile::new(
        "a",
        "0 = integration::Test { x: -5, y: 5 }
        a_ref = $0",
        vec![
            Box::new(|object, ctx| {
                assert!(object.top_level);
                (expected_value_fn(Test { x: -5, y: 5 }))(object, ctx)
            }),
            expected_value_fn(TestRef("a".into())),
        ],
    );
    // test non-top-level file
    let ac = &TestFile::new(
        "a::c",
        "0 = integration::Test { x: -5, y: 5 }\n\
        ref_local = $0\n\
        ref_full = $a::c",
        vec![
            Box::new(|object, ctx| {
                assert!(object.top_level);
                (expected_value_fn(Test { x: -5, y: 5 }))(object, ctx)
            }),
            expected_value_fn(TestRef("a::c".into())),
            expected_value_fn(TestRef("a::c".into())),
        ],
    );
    // test refering to them from a separate file
    let b = &test_file!(
        "b",
        "0 = $a\n\
         c_ref = $a::c",
        TestRef("a".into()),
        TestRef("a::c".into()),
    );

    test_reload(
        &|ctx| {
            ctx.register_type::<Test, _>();
        },
        &[a, ac, b],
        &[a, ac, b],
    );
}

#[test]
#[should_panic = "'a::1' refers to an existing asset"]
fn duplicate_name_after_simplification() {
    let a = &TestFile::new(
        "a",
        "0 = integration::Test { x: -5, y: 5 }\n\
        1 = integration::Test { x: -5, y: 5 }", // local and full path are the same here
        vec![
            Box::new(|object, ctx| {
                assert!(object.top_level);
                (expected_value_fn(Test { x: -5, y: 5 }))(object, ctx)
            }),
            Box::new(|object, ctx| {
                assert!(!object.top_level);
                (expected_value_fn(Test { x: -5, y: 5 }))(object, ctx)
            }),
        ],
    );
    // test non-top-level file
    let a1 = &TestFile::new(
        "a::1",
        "0 = integration::Test { x: -5, y: 5 }",
        vec![Box::new(|object, ctx| {
            assert!(object.top_level);
            (expected_value_fn(Test { x: -5, y: 5 }))(object, ctx)
        })],
    );

    test_load(
        &|ctx| {
            ctx.register_type::<Test, _>();
        },
        &[a, a1],
    );
}

/// Paths won't collide after simplification but we don't want to allow names of objects in the
/// same file to collide.
#[test]
#[should_panic = "Identifier '0' is only allowed for the first item"]
fn duplicate_name_before_simplification() {
    let a = &TestFile::new(
        "a",
        "0 = integration::Test { x: -5, y: 5 }\n\
        0 = integration::Test { x: -5, y: 5 }",
        vec![
            Box::new(|object, ctx| {
                assert!(object.top_level);
                (expected_value_fn(Test { x: -5, y: 5 }))(object, ctx)
            }),
            Box::new(|object, ctx| {
                assert!(!object.top_level);
                (expected_value_fn(Test { x: -5, y: 5 }))(object, ctx)
            }),
        ],
    );

    test_load(
        &|ctx| {
            ctx.register_type::<Test, _>();
        },
        &[a],
    );
}

#[test]
#[should_panic = "The first item must have '0' as the identifier"]
fn special_identifier_required_for_first_object() {
    let a = &TestFile::new(
        "a",
        "1 = integration::Test { x: -5, y: 5 }",
        vec![Box::new(|object, ctx| {
            assert!(object.top_level);
            (expected_value_fn(Test { x: -5, y: 5 }))(object, ctx)
        })],
    );

    test_load(
        &|ctx| {
            ctx.register_type::<Test, _>();
        },
        &[a],
    );
}
