mod parser;
mod value;

use std::borrow::Cow;

use chumsky::error::Rich;
pub use parser::{ParserSource, parser};

pub use value::*;

use crate::{
    BaubleContext, Span, SpanExt,
    error::{BaubleError, Level},
};

impl BaubleError for Rich<'static, char, Span> {
    fn msg_general(&self, _: &BaubleContext) -> crate::error::ErrorMsg {
        Cow::Borrowed("Parser error").spanned(*self.span())
    }

    fn msgs_specific(
        &self,
        _: &BaubleContext,
    ) -> Vec<(crate::error::ErrorMsg, crate::error::Level)> {
        std::iter::once((
            Cow::<str>::Owned(self.reason().to_string()).spanned(*self.span()),
            Level::Error,
        ))
        .chain(self.contexts().map(|(msg, span)| {
            (
                Cow::<str>::Owned(msg.to_string()).spanned(*span),
                Level::Info,
            )
        }))
        .collect()
    }
}
