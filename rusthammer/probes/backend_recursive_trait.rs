//! Diagnostic: passing a recursive rule's own interpreter dictionary to its body.
#![no_std]

pub struct Rule;
pub struct Direct;

pub trait Eval<B> {
    fn eval(&self, backend: &mut B, count: u8) -> u8;
}

fn body<B>(backend: &mut B, count: u8) -> u8
where
    Rule: Eval<B>,
{
    if count == 0 {
        0
    } else {
        Rule.eval(backend, count - 1)
    }
}

impl Eval<Direct> for Rule {
    fn eval(&self, backend: &mut Direct, count: u8) -> u8 {
        body(backend, count)
    }
}

pub fn run(count: u8) -> u8 {
    Rule.eval(&mut Direct, count)
}
