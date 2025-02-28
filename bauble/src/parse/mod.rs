mod parser;
mod value;

use std::borrow::Cow;

use chumsky::error::Rich;
pub use parser::{ParserSource, parser};

pub use value::*;

use crate::{
    Span, SpanExt,
    error::{BaubleError, Level},
};

impl BaubleError for Rich<'_, char, Span> {
    fn msg_general(&self) -> crate::error::ErrorMsg {
        Cow::Borrowed("Parser error").spanned(self.span().clone())
    }

    fn msgs_specific(&self) -> Vec<(crate::error::ErrorMsg, crate::error::Level)> {
        std::iter::once((
            Cow::<str>::Owned(self.reason().to_string()).spanned(self.span().clone()),
            Level::Error,
        ))
        .chain(self.contexts().map(|(msg, span)| {
            (
                Cow::<str>::Owned(msg.to_string()).spanned(span.clone()),
                Level::Info,
            )
        }))
        .collect()
    }
}
