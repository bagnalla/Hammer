//! Native-valid candidates retained as expected extraction failures.

use rusthammer::{
    choice, seq, Cursor, Direct, Epsilon, Eval, Grammar, Ignore, Literal, ParseContext,
    ParseOutcome, Parser,
};

pub struct Named;
impl<'input> Grammar<'input> for Named {
    type Output = ();
}
impl<'input> Eval<'input, Direct> for Named {
    fn eval(
        &self,
        backend: &mut Direct,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<()> {
        let token = Literal::new(8, u64::from(b'a')).unwrap();
        let body = choice(
            Ignore {
                parser: seq(token, Named),
            },
            Epsilon,
        );
        body.eval(backend, input, cursor, context)
    }
}
pub fn named(input: &[u8], cursor: Cursor, context: ParseContext) -> ParseOutcome<()> {
    Named.eval(&mut Direct, input, cursor, context)
}

/// The blanket `Parser` entry point makes the evaluator implementation reachable.
/// It still contains the same recursive implementation/method dependency.
pub fn named_parser(input: &[u8], cursor: Cursor, context: ParseContext) -> ParseOutcome<()> {
    Named.parse_with(input, cursor, context)
}

pub struct Call<F>(F);
impl<'input, F, T> Grammar<'input> for Call<F>
where
    F: Fn(&'input [u8], Cursor, ParseContext) -> ParseOutcome<T>,
{
    type Output = T;
}
impl<'input, F, T> Eval<'input, Direct> for Call<F>
where
    F: Fn(&'input [u8], Cursor, ParseContext) -> ParseOutcome<T>,
{
    fn eval(
        &self,
        _: &mut Direct,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<T> {
        (self.0)(input, cursor, context)
    }
}
pub fn closure(input: &[u8], cursor: Cursor, context: ParseContext) -> ParseOutcome<()> {
    let token = Literal::new(8, u64::from(b'a')).unwrap();
    let recur = Call(|input, cursor, context| closure(input, cursor, context));
    choice(
        Ignore {
            parser: seq(token, recur),
        },
        Epsilon,
    )
    .eval(&mut Direct, input, cursor, context)
}
pub fn function_item(input: &[u8], cursor: Cursor, context: ParseContext) -> ParseOutcome<()> {
    let token = Literal::new(8, u64::from(b'a')).unwrap();
    choice(
        Ignore {
            parser: seq(token, Call(function_item)),
        },
        Epsilon,
    )
    .eval(&mut Direct, input, cursor, context)
}

pub struct Pointer(for<'input> fn(&'input [u8], Cursor, ParseContext) -> ParseOutcome<()>);
impl<'input> Grammar<'input> for Pointer {
    type Output = ();
}
impl<'input> Eval<'input, Direct> for Pointer {
    fn eval(
        &self,
        _: &mut Direct,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<()> {
        (self.0)(input, cursor, context)
    }
}
pub fn pointer(input: &[u8], cursor: Cursor, context: ParseContext) -> ParseOutcome<()> {
    let token = Literal::new(8, u64::from(b'a')).unwrap();
    choice(
        Ignore {
            parser: seq(token, Pointer(pointer)),
        },
        Epsilon,
    )
    .eval(&mut Direct, input, cursor, context)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn candidates() {
        let expected = ParseOutcome::Success(Cursor { byte: 3, bit: 0 }, ());
        assert_eq!(
            pointer(b"aaax", Cursor::start(), ParseContext::FINAL),
            expected
        );
        assert_eq!(
            named(b"aaax", Cursor::start(), ParseContext::FINAL),
            expected
        );
        assert_eq!(
            named_parser(b"aaax", Cursor::start(), ParseContext::FINAL),
            expected
        );
        assert_eq!(
            closure(b"aaax", Cursor::start(), ParseContext::FINAL),
            expected
        );
        assert_eq!(
            function_item(b"aaax", Cursor::start(), ParseContext::FINAL),
            expected
        );
    }
}
