use bauble::Bauble;

#[derive(Bauble, PartialEq, Debug)]
struct Test {
    x: i32,
    y: u32,
}

#[test]
pub fn ref_implicit() {
    bauble::bauble_test!(
        [Test]
        "test = lang::Test{ x: -5, y: 5 }\n\
        r = $test"
        [
            Test { x: -5, y: 5 },
            Test { x: -5, y: 5 },
        ]
    );
}

#[test]
pub fn explicit_implicit() {
    bauble::bauble_test!(
        [Test]
        "test = lang::Test{ x: -2, y: 2 }\n\
        r: Ref<lang::Test> = $test"
        [
            Test { x: -2, y: 2 },
            Test { x: -2, y: 2 },
        ]
    );
}

#[test]
pub fn ref_explicit_out_of_order() {
    bauble::bauble_test!(
        TEST0
        [Test]
        [
            "test = lang::Test{ x: -5, y: 5 }",
            "r: Ref<lang::Test> = $test"
        ]
        [
            Test { x: -5, y: 5 },
            Test { x: -5, y: 5 },
        ]
    );

    bauble::bauble_test!(
        TEST1
        [Test]
        [
            "r: Ref<lang::Test> = $test",
            "test = lang::Test{ x: -5, y: 5 }"
        ]
        [
            Test { x: -5, y: 5 },
            Test { x: -5, y: 5 },
        ]
    );
}

#[test]
pub fn ref_implicit_out_of_order() {
    bauble::bauble_test!(
        TEST0
        [Test]
        [
            "test = lang::Test{ x: -5, y: 5 }",
            "r = $test::test"
        ]
        [
            Test { x: -5, y: 5 },
            Test { x: -5, y: 5 },
        ]
    );

    bauble::bauble_test!(
        TEST1
        [Test]
        [
            "r = $test::test",
            "test = lang::Test{ x: -5, y: 5 }"
        ]
        [
            Test { x: -5, y: 5 },
            Test { x: -5, y: 5 },
        ]
    );
}
