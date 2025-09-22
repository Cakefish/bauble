use std::collections::HashMap;

use bauble::{Bauble, SpannedValue, bauble_test};

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
        test = derive::Test { x: -5, y: 5, z: Some(true) }
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

#[test]
fn test_default() {
    #[derive(Bauble, PartialEq, Debug, Default)]
    struct Foo(u32, #[bauble(attribute = foo, default)] u32);

    #[derive(Bauble, PartialEq, Debug)]
    #[bauble(flatten)]
    struct Bar(Foo, #[bauble(attribute = test, default)] u32);

    bauble_test!(
        [Foo, Bar]
        r#"
        use derive::{Foo, Bar};

        a: Foo = default
        b: Bar = default
        c: Foo = #[foo = 2] default
        d: Bar = #[test = 10] default
        e: Bar = #[test = 11, foo = 33] default
        f = <Bar> default
        "#
        [
            Foo(0, 0),
            Bar(Foo(0, 0), 0),
            Foo(0, 2),
            Bar(Foo(0, 0), 10),
            Bar(Foo(0, 33), 11),
            Bar(Foo(0, 0), 0),
        ]
    );
}

#[test]
fn test_trait() {
    use bauble::path::TypePath;
    use bauble::types::{BaubleTrait, Type, TypeKind, TypeMeta, TypeRegistry};

    trait TestTrait: std::fmt::Debug {
        fn dyn_eq(&self, other: &dyn TestTrait) -> bool;

        fn as_any(&self) -> &dyn std::any::Any;
    }

    impl BaubleTrait for dyn TestTrait {
        const BAUBLE_PATH: &'static str = "derive::TestTrait";
    }

    #[derive(Debug)]
    struct Trans(Box<dyn TestTrait>);

    impl PartialEq for Trans {
        fn eq(&self, other: &Self) -> bool {
            self.0.dyn_eq(&*other.0)
        }
    }

    impl Bauble<'_> for Trans {
        fn construct_type(registry: &mut TypeRegistry) -> Type {
            let tr = registry.get_or_register_trait::<dyn TestTrait>();

            Type {
                meta: TypeMeta {
                    path: TypePath::new("derive::Trans")
                        .expect("This is a valid path")
                        .to_owned(),
                    traits: vec![tr],

                    ..Default::default()
                },
                kind: TypeKind::Transparent(tr.into()),
            }
        }

        fn from_bauble(
            val: bauble::Val,
            allocator: &bauble::DefaultAllocator,
        ) -> Result<
            <bauble::DefaultAllocator as bauble::BaubleAllocator>::Out<Self>,
            bauble::ToRustError,
        > {
            let s = val.span();
            if let bauble::Value::Transparent(v) = val.value.value {
                let ctx = TEST_CTX.get().unwrap().read().unwrap();

                let types = ctx.type_registry();

                let rust_ty = types.find_rust_type(*v.ty).unwrap();

                use std::any::TypeId;

                let v: Box<dyn TestTrait> = if rust_ty == TypeId::of::<Foo>() {
                    Box::new(Foo::from_bauble(*v, allocator)?)
                } else if rust_ty == TypeId::of::<Bar>() {
                    Box::new(Bar::from_bauble(*v, allocator)?)
                } else {
                    return Err(Self::error(
                        s,
                        bauble::ToRustErrorKind::WrongType { found: val.ty },
                    ));
                };

                Ok(Trans(v))
            } else {
                Err(Self::error(
                    s,
                    bauble::ToRustErrorKind::WrongType { found: val.ty },
                ))
            }
        }
    }

    #[derive(Bauble, PartialEq, Debug)]
    #[bauble(traits(TestTrait))]
    pub struct Foo(u32);

    impl TestTrait for Foo {
        fn dyn_eq(&self, other: &dyn TestTrait) -> bool {
            match other.as_any().downcast_ref::<Self>() {
                Some(v) => v == self,
                None => false,
            }
        }

        fn as_any(&self) -> &dyn std::any::Any {
            self
        }
    }

    #[derive(Bauble, PartialEq, Debug)]
    #[bauble(flatten)]
    #[bauble(traits(TestTrait))]
    pub struct Bar(String);

    impl TestTrait for Bar {
        fn dyn_eq(&self, other: &dyn TestTrait) -> bool {
            match other.as_any().downcast_ref::<Self>() {
                Some(v) => v == self,
                None => false,
            }
        }

        fn as_any(&self) -> &dyn std::any::Any {
            self
        }
    }

    bauble_test!(
        TEST_CTX
        [Trans, Foo, Bar]
        r#"
            use derive::{Trans, Foo, Bar};

            a: Trans = Foo(32)

            b: Trans = <Bar> "meow"
        "#
        [Trans(Box::new(Foo(32))), Trans(Box::new(Bar("meow".to_string())))]
    );
}

#[test]
fn test_generic() {
    #[derive(Bauble, Debug, PartialEq, Eq)]
    struct Foo<T: for<'a> Bauble<'a>>(T);

    #[derive(Bauble, Debug, PartialEq, Eq)]
    struct Bar(u32);

    #[derive(Bauble, Debug, PartialEq, Eq)]
    struct Str(String);

    bauble_test!(
        [Foo<Bar>, Foo<Str>, Bar, Str]
        r#"
        use derive::{Foo, Bar, Str};

        a: Foo<Bar> = Foo(Bar(24))
        b: Foo<Str> = Foo(Str("test"))
        "#
        [
            Foo(Bar(24)),
            Foo(Str(String::from("test"))),
        ]
    );

    let ctx = __TEST_CTX.get().unwrap().read().unwrap();
    let Some(ty) = ctx
        .type_registry()
        .get_type::<Foo<Bar>, bauble::DefaultAllocator>()
    else {
        panic!("no!!");
    };
    println!("{ty:?}");

    panic!();
}
