use bauble::{Bauble, Ref, path::TypePath};

#[derive(Bauble, PartialEq, Debug)]
struct Test {
    x: i32,
    y: u32,
}

#[test]
pub fn ref_implicit_type() {
    bauble::bauble_test!(
        [Test]
        "test = lang::Test{ x: -5, y: 5 }\n\
        r = $test"
        [
            Test { x: -5, y: 5 },
            Ref::<Test>::from_path(TypePath::new_unchecked("test::test").to_owned()),
        ]
    );

    bauble::bauble_test!(
        [Test]
        "r = $test::test\n\
        test = lang::Test{ x: -5, y: 5 }"
        [
            Ref::<Test>::from_path(TypePath::new_unchecked("test::test").to_owned()),
            Test { x: -5, y: 5 },
        ]
    );
}

#[test]
pub fn ref_explicit_type() {
    bauble::bauble_test!(
        [Test]
        "test = lang::Test{ x: -2, y: 2 }\n\
        r: Ref<lang::Test> = $test"
        [
            Test { x: -2, y: 2 },
            Ref::<Test>::from_path(TypePath::new_unchecked("test::test").to_owned()),
        ]
    );

    bauble::bauble_test!(
        [Test]
        "r: Ref<lang::Test> = $test::test\n\
        test = lang::Test{ x: -2, y: 2 }"
        [
            Ref::<Test>::from_path(TypePath::new_unchecked("test::test").to_owned()),
            Test { x: -2, y: 2 },
        ]
    );
}

#[test]
pub fn ref_explicit_type_multiple_files() {
    bauble::bauble_test!(
        [Test]
        [
            "test = lang::Test{ x: -5, y: 5 }",
            "r: Ref<lang::Test> = $test::test"
        ]
        [
            Test { x: -5, y: 5 },
            Ref::<Test>::from_path(TypePath::new_unchecked("test::test").to_owned()),
        ]
    );

    bauble::bauble_test!(
        [Test]
        [
            "r: Ref<lang::Test> = $test::test",
            "test = lang::Test{ x: -5, y: 5 }"
        ]
        [
            Ref::<Test>::from_path(TypePath::new_unchecked("test::test").to_owned()),
            Test { x: -5, y: 5 },
        ]
    );
}

#[test]
pub fn ref_implicit_type_multiple_files() {
    bauble::bauble_test!(
        [Test]
        [
            "test = lang::Test{ x: -5, y: 5 }",
            "r = $test::test"
        ]
        [
            Test { x: -5, y: 5 },
            Ref::<Test>::from_path(TypePath::new_unchecked("test::test").to_owned()),
        ]
    );

    bauble::bauble_test!(
        [Test]
        [
            "r = $test::test",
            "test = lang::Test{ x: -5, y: 5 }"
        ]
        [
            Ref::<Test>::from_path(TypePath::new_unchecked("test::test").to_owned()),
            Test { x: -5, y: 5 },
        ]
    );
}

#[test]
#[should_panic]
pub fn ref_explicit_type_incorrect() {
    #[derive(Bauble, PartialEq, Eq, Debug)]
    struct Incorrect(u32);

    bauble::bauble_test!(
        [Test, Incorrect]
        "i: Incorrect = Incorrect(0)\n\
        r: Ref<Incorrect> = $test::test\n\
        test = lang::Test{ x: -2, y: 2 }"
        [
            Incorrect(0),
            Ref::<Test>::from_path(TypePath::new_unchecked("test::test").to_owned()),
            Test { x: -2, y: 2 },
        ]
    );
}
