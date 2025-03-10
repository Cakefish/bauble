use std::borrow::Cow;

use ariadne::Report;

use crate::{AssetContext, Span, Spanned, bauble_context::AssetContextCache, types::TypeRegistry};

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

pub trait BaubleError {
    fn level(&self) -> Level {
        Level::Error
    }

    fn can_ignore(&self) -> bool {
        !matches!(self.level(), Level::Error)
    }

    fn msg_general(&self, types: &TypeRegistry) -> ErrorMsg;

    fn msgs_specific(&self, types: &TypeRegistry) -> Vec<(ErrorMsg, Level)>;

    fn help(&self) -> Option<Cow<'static, str>> {
        None
    }

    fn report(&self, types: &TypeRegistry) -> Report<'_, Span> {
        let msg = self.msg_general(types);
        let mut report =
            Report::build(self.level().report_kind(), msg.span).with_message(msg.value);

        if let Some(help) = self.help() {
            report.set_help(help);
        }

        for (msg, level) in self.msgs_specific(types) {
            report.add_label(
                ariadne::Label::new(msg.span)
                    .with_message(msg.value.clone())
                    .with_color(level.color()),
            );
        }

        report
            .with_config(ariadne::Config::new().with_compact(true))
            .finish()
    }
}

impl<B: BaubleError> BaubleError for Box<B> {
    fn msg_general(&self, registry: &TypeRegistry) -> ErrorMsg {
        B::msg_general(self, registry)
    }

    fn msgs_specific(&self, registry: &TypeRegistry) -> Vec<(ErrorMsg, Level)> {
        B::msgs_specific(self, registry)
    }

    fn level(&self) -> Level {
        B::level(self)
    }

    fn can_ignore(&self) -> bool {
        B::can_ignore(self)
    }

    fn help(&self) -> Option<Cow<'static, str>> {
        B::help(self)
    }

    fn report(&self, registry: &TypeRegistry) -> Report<'_, Span> {
        B::report(self, registry)
    }
}

pub struct BaubleErrors<'a>(Vec<Box<dyn BaubleError + 'a>>);

impl BaubleErrors<'_> {
    fn for_reports(
        &self,
        mut handle_report: impl for<'a> FnMut(Report<'a, Span>),
        ctx: &impl AssetContext,
    ) {
        for error in self.0.iter() {
            handle_report(BaubleError::report(error.as_ref(), ctx.type_registry()))
        }
    }

    pub fn print_errors(&self, ctx: &impl AssetContext) {
        self.for_reports(
            |report| {
                let _ = report.eprint(AssetContextCache(ctx));
            },
            ctx,
        );
    }

    pub fn write_errors<W>(&self, ctx: &impl AssetContext, w: &mut W)
    where
        W: std::io::Write,
    {
        self.for_reports(
            |report| {
                let _ = report.write(AssetContextCache(ctx), &mut *w);
            },
            ctx,
        );
    }
}

impl<'a, B: BaubleError + 'a> From<B> for BaubleErrors<'a> {
    fn from(value: B) -> Self {
        Self(vec![Box::new(value)])
    }
}

impl<'a, B: BaubleError + 'a> From<Vec<B>> for BaubleErrors<'a> {
    fn from(value: Vec<B>) -> Self {
        Self(
            value
                .into_iter()
                .map(|err| Box::new(err) as Box<dyn BaubleError>)
                .collect(),
        )
    }
}

pub fn print_errors<'a, T>(
    res: Result<T, impl Into<BaubleErrors<'a>>>,
    ctx: &impl AssetContext,
) -> Option<T> {
    res.map_err(|errors| {
        let errors: BaubleErrors = errors.into();
        errors.print_errors(ctx)
    })
    .ok()
}
