#![allow(clippy::type_complexity)]
use bauble::Bauble;
use bauble::BaubleContext;
use bauble::Object;
use bauble::path::TypePath;

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
        let read_value = bauble::print_errors(result, ctx).unwrap();
        assert_eq!(&read_value, &expected_value);
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

fn test_reload(
    register_types: &dyn Fn(&mut bauble::BaubleContextBuilder),
    start: &[&TestFile],
    new: &[&TestFile],
) {
    // Test that parsed objects convert into typed values that match the provided test values.
    let compare_objects = |objects: Vec<Object>, files: &[&TestFile], ctx: &BaubleContext| {
        let mut objects = objects.into_iter();
        for test_value in files.iter().flat_map(|f| &f.expected_values) {
            let object = objects.next().expect("Not as many objects as test expects");
            test_value(object, ctx);
        }

        if objects.next().is_some() {
            panic!("More objects than test expects");
        }
    };

    let mut ctx = bauble::BaubleContextBuilder::new();
    register_types(&mut ctx);
    let mut ctx = ctx.build();
    ctx.type_registry()
        .validate(true)
        .expect("Invalid type registry");

    // Test initial parsing from source
    for file in start {
        ctx.register_file(file.path.borrow(), &file.content); // format!("\n{}\n", inner_content));
    }

    let (objects, errors) = ctx.load_all();
    if !errors.is_empty() {
        bauble::print_errors(Err::<(), _>(errors), &ctx);
        panic!("Error converting");
    }
    compare_objects(objects, start, &ctx);

    // Test reloading with new content and new files that are nested as submodules.
    let (objects, errors) = ctx.reload_paths(new.iter().map(|f| (f.path.borrow(), &f.content)));
    if !errors.is_empty() {
        bauble::print_errors(Err::<(), _>(errors), &ctx);
        panic!("Error converting reload");
    }
    compare_objects(objects, new, &ctx);
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
fn duplicate_objects() {
    // TODO: would be better for this to fail rather than taking the last object? What if the
    // objects are different types and something references the first one?
    bauble::bauble_test!(
        [Test]
        "test = integration::Test{ x: -5, y: 5 }\n\
        test = integration::Test{ x: -5, y: 4 }"
        [Test { x: -5, y: 4 }]
    );
}
