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

/// Makes the implementation reachable from outside its own method.
/// This changes the extraction diagnostic, but does not remove the cycle.
pub fn indirect(count: u8) -> u8 {
    body(&mut Direct, count)
}

/// Control: ordinary recursion with the same native result.
pub fn plain(count: u8) -> u8 {
    if count == 0 {
        0
    } else {
        plain(count - 1)
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn all_counts() {
        for count in 0..=u8::MAX {
            assert_eq!(super::run(count), 0);
            assert_eq!(super::indirect(count), 0);
            assert_eq!(super::plain(count), 0);
        }
    }
}
