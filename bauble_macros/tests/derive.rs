use std::collections::HashMap;

use bauble::{Bauble, bauble_context::BaubleContextBuilder, error::print_errors, path::TypePath};

macro_rules! bauble_test {
    ([$($ty:ty),* $(,)?] $source:literal [$($expr:expr),* $(,)?]) => {
        {
            let mut ctx = BaubleContextBuilder::new();
            $(ctx.register_type::<$ty, _>();)*
            let mut ctx = ctx.build();
            ctx.register_file(TypePath::new("test").unwrap(), format!("\n{}\n", $source));

            let (objects, errors) = ctx.load_all();

            ctx.debug_node();

            if !errors.is_empty() {
                print_errors(Err::<(), _>(errors), &ctx);

                panic!("Error converting");
            }

            let mut objects = objects.into_iter();
            $(
                let value = objects.next().expect("Not as many objects as test expr in bauble test?");
                let mut read_value = $expr;
                let test_value = std::mem::replace(&mut read_value, print_errors(Bauble::from_bauble(value.value, &::bauble::DefaultAllocator), &ctx).unwrap());


                assert_eq!(
                    read_value,
                    test_value,
                );
            )*
        }
    };
}

#[test]
fn test_struct() {
    #[derive(Bauble, PartialEq, Debug)]
    struct Test {
        x: i32,
        y: u32,
        z: Option<bool>,
    }

    bauble_test!(
        [Test]
        r#"
        test = derive::Test { x: -5, y: 5, z: std::Option::Some(true) }
        "#
        [Test {
            x: -5,
            y: 5,
            z: Some(true)
        }]
    );
}

#[test]
fn test_tuple() {
    #[derive(Bauble, PartialEq, Debug)]
    struct Test(i32, u32);

    bauble_test!(
        [Test]
        "test = derive::Test(-5, 5)"
        [Test(-5, 5)]
    );
}

#[test]
fn test_enum() {
    #[derive(Bauble, PartialEq, Debug)]
    enum Test {
        Foo(i32, u32),
        Bar { x: i32, y: u32 },
        Baz,
    }

    bauble_test!(
        [Test]
        r#"
        use derive::Test;

        a = Test::Foo(-10, 2)
        b = Test::Bar { x: -5, y: 5 }
        c = Test::Baz
        "#
        [
            Test::Foo(-10, 2),
            Test::Bar { x: -5, y: 5 },
            Test::Baz,
        ]
    );
}

#[test]
fn test_flattened() {
    #[derive(Bauble, PartialEq, Debug)]
    #[bauble(flatten)]
    enum Test {
        Foo(i32),
        Bar { x: bool },
    }

    #[derive(Bauble, PartialEq, Debug)]
    #[bauble(flatten)]
    struct Test2 {
        #[bauble(attribute, default)]
        count: u32,
        name: String,
    }

    bauble_test!(
        [Test, Test2]
        r#"
        use derive::{Test, Test2};

        a: Test = -10
        b: Test = true
        c: Test2 = #[count = 10] "foo"
        d: Test2 = "bar"
        "#
        [
            Test::Foo(-10),
            Test::Bar { x: true },
            Test2 {
                count: 10,
                name: "foo".to_string(),
            },
            Test2 {
                count: 0,
                name: "bar".to_string(),
            }
        ]
    );
}

#[test]
fn test_std_types() {
    #[derive(Bauble, PartialEq, Debug)]
    struct Test {
        a: Vec<(u32, i32)>,
        b: HashMap<String, Vec<bool>>,
        c: HashMap<[u32; 3], [Option<String>; 3]>,
    }

    bauble_test!(
        [Test]
        r#"
        use std::Option::*;

        copy key = "key"
        copy value = Some("value")

        test = derive::Test {
            a: [(2, 0), (1, -1), (5, 10)],
            b: {
                $key: [true, true, false],
                "no key": [false, true],
            },
            c: {
                [1, 2, 3]: [$value, None, Some("hi")],
            },
        }
        "#
        [
            Test {
                a: vec![(2, 0), (1, -1), (5, 10)],
                b: HashMap::from_iter([
                    ("key".to_string(), vec![true, true, false]),
                    ("no key".to_string(), vec![false, true]),
                ]),
                c: HashMap::from_iter([
                    ([1, 2, 3], [Some("value".to_string()), None, Some("hi".to_string())]),
                ]),
            },
        ]
    );
}
