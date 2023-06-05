use bauble::FromBauble;

fn simple_convert<'a, T: FromBauble<'a>>(
    src: &str,
    object_name: &str,
    alloc: &'a bauble::DefaultAllocator,
) -> Result<T, Box<bauble::DeserializeError>> {
    let objects = bauble::simple_convert(src).map_err(bauble::DeserializeError::Convertion)?;
    for object in objects {
        if object.object_path.ends_with(object_name) {
            return Ok(T::from_bauble(object.value, alloc)?);
        }
    }
    panic!("`object` not found");
}

#[test]
fn test_struct() {
    #[derive(FromBauble, PartialEq, Debug)]
    struct Test {
        x: i32,
        y: u32,
    }
    assert_eq!(
        Ok(Test { x: -5, y: 5 }),
        simple_convert("test = derive::Test { x: -5, y: 5 }", "test", &bauble::DefaultAllocator)
    );
}

#[test]
fn test_tuple() {
    #[derive(FromBauble, PartialEq, Debug)]
    struct Test(i32, u32);
    assert_eq!(
        Ok(Test(-5, 5)),
        simple_convert("test = derive::Test(-5, 5)", "test", &bauble::DefaultAllocator)
    );
}

#[test]
fn test_flattened() {
    #[derive(FromBauble, PartialEq, Debug)]
    #[bauble(flatten)]
    enum Test {
        Foo(i32, u32),
        Bar { x: i32, y: u32 },
        Baz,
    }
    assert_eq!(
        Ok(Test::Foo(-10, 2)),
        simple_convert("test = derive::Test(-10, 2)", "test", &bauble::DefaultAllocator)
    );
    assert_eq!(
        Ok(Test::Bar { x: -5, y: 5 }),
        simple_convert("test = derive::Test { x: -5, y: 5 }", "test", &bauble::DefaultAllocator)
    );
    assert_eq!(Ok(Test::Baz), simple_convert("test = derive::Test", "test", &bauble::DefaultAllocator));
}
