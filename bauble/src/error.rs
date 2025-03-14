use std::borrow::Cow;

use ariadne::Report;

use crate::{
    Span, Spanned,
    bauble_context::{BaubleContext, BaubleContextCache},
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Level {
    Info,
    Warning,
    Error,
}

impl Level {
    fn color(&self) -> ariadne::Color {
        match self {
            Level::Info => ariadne::Color::Blue,
            Level::Warning => ariadne::Color::Yellow,
            Level::Error => ariadne::Color::Red,
        }
    }

    fn report_kind(&self) -> ariadne::ReportKind<'static> {
        match self {
            Level::Info => ariadne::ReportKind::Advice,
            Level::Warning => ariadne::ReportKind::Warning,
            Level::Error => ariadne::ReportKind::Error,
        }
    }
}

pub type ErrorMsg = Spanned<Cow<'static, str>>;

pub trait BaubleError: 'static {
    fn level(&self) -> Level {
        Level::Error
    }

    fn can_ignore(&self) -> bool {
        !matches!(self.level(), Level::Error)
    }

    fn msg_general(&self, ctx: &BaubleContext) -> ErrorMsg;

    fn msgs_specific(&self, ctx: &BaubleContext) -> Vec<(ErrorMsg, Level)>;

    fn help(&self, _ctx: &BaubleContext) -> Option<Cow<'static, str>> {
        None
    }

    fn report(&self, ctx: &BaubleContext) -> Report<'_, Span> {
        let msg = self.msg_general(ctx);
        let mut report =
            Report::build(self.level().report_kind(), msg.span).with_message(msg.value);

        if let Some(help) = self.help(ctx) {
            report.set_help(help);
        }

        for (msg, level) in self.msgs_specific(ctx) {
            report.add_label(
                ariadne::Label::new(msg.span)
                    .with_message(msg.value.clone())
                    .with_color(level.color()),
            );
        }

        report
            .with_config(ariadne::Config::new().with_index_type(ariadne::IndexType::Byte))
            .finish()
    }
}

impl<B: BaubleError> BaubleError for Box<B> {
    fn msg_general(&self, ctx: &BaubleContext) -> ErrorMsg {
        B::msg_general(self, ctx)
    }

    fn msgs_specific(&self, ctx: &BaubleContext) -> Vec<(ErrorMsg, Level)> {
        B::msgs_specific(self, ctx)
    }

    fn level(&self) -> Level {
        B::level(self)
    }

    fn can_ignore(&self) -> bool {
        B::can_ignore(self)
    }

    fn help(&self, ctx: &BaubleContext) -> Option<Cow<'static, str>> {
        B::help(self, ctx)
    }

    fn report(&self, ctx: &BaubleContext) -> Report<'_, Span> {
        B::report(self, ctx)
    }
}

pub struct BaubleErrors(Vec<Box<dyn BaubleError>>);

impl BaubleErrors {
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
    pub fn empty() -> Self {
        Self(Vec::new())
    }

    pub fn extend(&mut self, other: BaubleErrors) {
        self.0.extend(other.0);
    }

    pub fn push<B: BaubleError>(&mut self, error: B) {
        self.0.push(Box::new(error))
    }

    fn for_reports(
        &self,
        mut handle_report: impl for<'b> FnMut(Report<'b, Span>),
        ctx: &BaubleContext,
    ) {
        for error in self.0.iter() {
            handle_report(BaubleError::report(error.as_ref(), ctx))
        }
    }

    pub fn print_errors(&self, ctx: &BaubleContext) {
        self.for_reports(
            |report| {
                let _ = report.eprint(BaubleContextCache(ctx));
            },
            ctx,
        );
    }

    pub fn write_errors<W>(&self, ctx: &BaubleContext, w: &mut W)
    where
        W: std::io::Write,
    {
        self.for_reports(
            |report| {
                let _ = report.write(BaubleContextCache(ctx), &mut *w);
            },
            ctx,
        );
    }
}

impl<B: BaubleError> From<B> for BaubleErrors {
    fn from(value: B) -> Self {
        Self(vec![Box::new(value)])
    }
}

impl<B: BaubleError> From<Vec<B>> for BaubleErrors {
    fn from(value: Vec<B>) -> Self {
        Self(
            value
                .into_iter()
                .map(|err| Box::new(err) as Box<dyn BaubleError>)
                .collect(),
        )
    }
}

pub fn print_errors<T>(res: Result<T, impl Into<BaubleErrors>>, ctx: &BaubleContext) -> Option<T> {
    res.map_err(|errors| {
        let errors: BaubleErrors = errors.into();
        errors.print_errors(ctx)
    })
    .ok()
}
