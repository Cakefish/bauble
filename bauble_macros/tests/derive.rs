use bauble::{Bauble, Source, error::print_errors, value::NoChecks};

fn simple_convert<'a, T: Bauble<'a>>(
    src: &str,
    object_name: &str,
    alloc: &'a bauble::DefaultAllocator,
) -> Option<T> {
    let ctx = NoChecks {
        src: Source::from(src.to_string()),
    };
    let objects = print_errors(bauble::convert("test", &ctx), &ctx)?;
    for object in objects {
        if object.object_path.ends_with(object_name) {
            return print_errors(T::from_bauble(object.value, alloc), &ctx);
        }
    }

    None
}

#[test]
fn test_struct() {
    #[derive(FromBauble, PartialEq, Debug)]
    struct Test {
        x: i32,
        y: u32,
        z: Option<bool>,
    }
    assert_eq!(
        Some(Test {
            x: -5,
            y: 5,
            z: Some(true)
        }),
        simple_convert(
            "test = derive::Test { x: -5, y: 5, z: Some(true) }",
            "test",
            &bauble::DefaultAllocator
        )
    );
}

#[test]
fn test_tuple() {
    #[derive(FromBauble, PartialEq, Debug)]
    struct Test(i32, u32);
    assert_eq!(
        Some(Test(-5, 5)),
        simple_convert(
            "test = derive::Test(-5, 5)",
            "test",
            &bauble::DefaultAllocator
        )
    );
}

/*
#[test]
fn test_enum() {
    #[derive(FromBauble, PartialEq, Debug)]
    enum Test {
        Foo(i32, u32),
        Bar { x: i32, y: u32 },
        Baz,
    }
    assert_eq!(
        Ok(Test::Foo(-10, 2)),
        simple_convert(
            "test = derive::Test(-10, 2)",
            "test",
            &bauble::DefaultAllocator
        )
    );
    assert_eq!(
        Ok(Test::Bar { x: -5, y: 5 }),
        simple_convert(
            "test = derive::Test { x: -5, y: 5 }",
            "test",
            &bauble::DefaultAllocator
        )
    );
    assert_eq!(
        Ok(Test::Baz),
        simple_convert("test = derive::Test", "test", &bauble::DefaultAllocator)
    );
}
*/

#[test]
fn test_flattened() {
    #[derive(FromBauble, PartialEq, Debug)]
    #[bauble(flatten)]
    enum Test {
        Foo(i32),
        Bar { x: bool },
    }
    assert_eq!(
        Some(Test::Foo(-10)),
        simple_convert("test = -10", "test", &bauble::DefaultAllocator)
    );
    assert_eq!(
        Some(Test::Bar { x: true }),
        simple_convert("test = true", "test", &bauble::DefaultAllocator)
    );

    #[derive(FromBauble, PartialEq, Debug)]
    #[bauble(flatten)]
    struct Test2 {
        #[bauble(attribute, default)]
        count: u32,
        name: String,
    }
    assert_eq!(
        Some(Test2 {
            count: 10,
            name: "foo".to_string()
        }),
        simple_convert(
            "test = #[count = 10] \"foo\"",
            "test",
            &bauble::DefaultAllocator
        )
    );
    assert_eq!(
        Some(Test2 {
            count: 0,
            name: "bar".to_string()
        }),
        simple_convert("test = \"bar\"", "test", &bauble::DefaultAllocator)
    );
}
