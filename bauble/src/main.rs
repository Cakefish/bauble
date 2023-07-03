use std::{fs::File, io::Read};

use ariadne::{Color, Label, Report, ReportKind, Source};
use bauble::{
    parse::{self},
    value::{convert_values, NoChecks, Symbols},
    DefaultAllocator, FromBauble,
};
use chumsky::Parser;

fn main() {
    let mut src = String::new();
    File::open("test.bbl")
        .unwrap()
        .read_to_string(&mut src)
        .unwrap();

    println!("Creating parser...");
    let parser = parse::parser();
    println!("Parsing file...");
    let result = parser.parse(src.as_str());
    println!("Done!");

    result.errors().for_each(|e| {
        Report::build(ReportKind::Error, (), e.span().start)
            .with_code(3)
            .with_message(e.to_string())
            .with_label(
                Label::new(e.span().into_range())
                    .with_message(e.reason().to_string())
                    .with_color(Color::Red),
            )
            .finish()
            .print(Source::from(&src))
            .unwrap();
    });

    let Some(values) = result.into_output() else { return };

    let ctx = NoChecks;

    let objects = convert_values("test.rsn".to_string(), values, &Symbols::new(&ctx));

    match objects {
        Ok(objects) => {
            println!(
                "res: {:?}",
                Vec::<i32>::from_bauble(objects[0].value.clone(), &DefaultAllocator)
            );
        }
        Err(e) => println!("Error: {e:?}"),
    }
}
