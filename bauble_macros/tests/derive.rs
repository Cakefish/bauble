use std::collections::HashMap;

use bauble::{Bauble, bauble_test};

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
        a: Vec<(u8, i32)>,
        b: HashMap<String, Vec<bool>>,
        c: HashMap<[u32; 3], [Option<String>; 3]>,
    }

    bauble_test!(
        [Test]
        r#"
        use std::Option::*;

        copy key = "🔑"
        copy value = Some("💖")

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
                    ("🔑".to_string(), vec![true, true, false]),
                    ("no key".to_string(), vec![false, true]),
                ]),
                c: HashMap::from_iter([
                    ([1, 2, 3], [Some("💖".to_string()), None, Some("hi".to_string())]),
                ]),
            },
        ]
    );
}

#[test]
fn test_complex_flatten() {
    #[derive(Bauble, PartialEq, Debug)]
    #[bauble(flatten)]
    struct Inner(
        u32,
        #[bauble(attribute = a, default)] u32,
        #[bauble(attribute = b)] u32,
    );

    #[derive(Bauble, PartialEq, Debug)]
    #[bauble(flatten)]
    struct Transparent(Inner, #[bauble(attribute = a)] u32);

    bauble_test!(
        [Transparent]
        r#"
        a: derive::Transparent = #[a = 1, b = 2] 3

        copy t = #[a = 2] 1

        // Since `b` isn't an attribute on `Transparent` that gets passed to `Inner`. And
        // since we already have `a` defined here, the `a` attribute on `copy t` gets
        // assigned to `Inner.1`.
        b: derive::Transparent = #[a = 4, b = 3] $t
        "#
        [
            Transparent(Inner(3, 0, 2), 1),
            Transparent(Inner(1, 2, 3), 4),
        ]
    );
}

#[test]
fn test_from() {
    #[derive(Bauble, PartialEq, Debug)]
    #[bauble(from = u32)]
    struct NumberRepr(String);

    impl From<u32> for NumberRepr {
        fn from(value: u32) -> Self {
            Self(value.to_string())
        }
    }

    #[derive(Bauble, PartialEq, Debug)]
    #[bauble(from = u32)]
    enum TestEnum {
        A(u32),
        B(u32),
    }

    impl From<u32> for TestEnum {
        fn from(value: u32) -> Self {
            if value < 1000 {
                Self::A(value)
            } else {
                Self::B(value - 1000)
            }
        }
    }

    bauble_test!(
        [NumberRepr, TestEnum]
        r#"
        a: derive::NumberRepr = 1553  

        b: derive::TestEnum = 555
        c: derive::TestEnum = 1333
        "#
        [NumberRepr("1553".to_string()), TestEnum::A(555), TestEnum::B(333)]
    );
}
