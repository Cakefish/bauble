use bauble::Bauble;

#[derive(Bauble, PartialEq, Debug)]
struct Test {
    x: i32,
    y: u32,
}

#[test]
pub fn ref_test() {
    bauble::bauble_test!(
        [Test]
        "test: syntax::Test = syntax::Test{ x: -5, y: 5 }\n\
        r: Ref<syntax::Test> = $test"
        [
            Test { x: -5, y: 5 },
            Test { x: -5, y: 5 },
        ]
    );
}
