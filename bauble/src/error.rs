use std::borrow::Cow;

use ariadne::Report;

use crate::{
    Span, Spanned,
    context::{BaubleContext, BaubleContextCache},
};

/// A custom error message.
#[derive(Clone, Debug, PartialEq)]
pub struct CustomError {
    /// The message to be displayed with the error.
    pub message: Cow<'static, str>,
    /// The level of the error.
    pub level: Level,
    /// Various additional diagnostics, highlighting areas of code.
    pub labels: Vec<(Spanned<Cow<'static, str>>, Level)>,
}

impl CustomError {
    #[allow(missing_docs)]
    pub fn new(s: impl Into<Cow<'static, str>>) -> Self {
        Self {
            message: s.into(),
            level: Level::Error,
            labels: Vec::new(),
        }
    }

    #[allow(missing_docs)]
    pub fn with_level(mut self, level: Level) -> Self {
        self.level = level;
        self
    }

    /// Highlights a span of code with an accompanying diagnostic message with a diagnostic relevance of `level`.
    #[allow(missing_docs)]
    pub fn with_label(mut self, s: Spanned<impl Into<Cow<'static, str>>>, level: Level) -> Self {
        self.labels.push((s.map(|s| s.into()), level));
        self
    }

    /// Highlights a span of code with an accompanying message.
    ///
    /// Shorthand for [`with_label`](Self::with_label) with an error level.
    #[allow(missing_docs)]
    pub fn with_err_label(self, s: Spanned<impl Into<Cow<'static, str>>>) -> Self {
        self.with_label(s, Level::Error)
    }
}

/// A level for diagnostics.
#[allow(missing_docs)]
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

/// A common trait implemented by various types used for diagnostics in Bauble.
pub trait BaubleError: 'static {
    /// The level of the diagnostic.
    ///
    /// By default, this is [`Error`](Level::Error)
    fn level(&self) -> Level {
        Level::Error
    }

    /// Can this diagnostic be ignored?
    ///
    /// By default, anything at a level of [`Error`](Level::Error) can not be ignored.
    fn can_ignore(&self) -> bool {
        !matches!(self.level(), Level::Error)
    }

    /// A more general and easily readable diagnostic message.
    fn msg_general(&self, ctx: &BaubleContext) -> ErrorMsg;

    /// A specific diagnostic message divided into multiple parts.
    fn msgs_specific(&self, ctx: &BaubleContext) -> Vec<(ErrorMsg, Level)>;

    /// Optionally provide a help for how to fix the diagnostic in case of an error or warning.
    fn help(&self, _ctx: &BaubleContext) -> Option<Cow<'static, str>> {
        None
    }

    /// Produces a [`Report`] from the diagnostic.
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

/// Maintains various amounts of errors produced by Bauble.
pub struct BaubleErrors(Vec<Box<dyn BaubleError>>);

impl BaubleErrors {
    #[allow(missing_docs)]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Creates an empty instance of `Self`.
    pub fn empty() -> Self {
        Self(Vec::new())
    }

    /// Extends `self` with all errors from `other`.
    pub fn extend(&mut self, other: BaubleErrors) {
        self.0.extend(other.0);
    }

    /// Appends `error` onto `self`.
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

    /// Will print all errors to stderr.
    pub fn print_errors(&self, ctx: &BaubleContext) {
        self.for_reports(
            |report| {
                let _ = report.eprint(BaubleContextCache(ctx));
            },
            ctx,
        );
    }

    /// Will write all errors to `w`.
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

/// Will print the errors of `res` in case of an error, otherwise, return the ok value of `res` of type `T`.
pub fn print_errors<T>(res: Result<T, impl Into<BaubleErrors>>, ctx: &BaubleContext) -> Option<T> {
    res.map_err(|errors| {
        let errors: BaubleErrors = errors.into();
        errors.print_errors(ctx)
    })
    .ok()
}
