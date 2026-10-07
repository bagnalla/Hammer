// Standalone driver for tools/compare_matches.py; not part of the library API.
#[allow(dead_code)]
#[path = "../../src/lib.rs"]
mod rusthammer;

use rusthammer::{
    And, ButNot, Cursor, Difference, Epsilon, Eval, Fail, Grammar, Left, Literal, Map,
    ParseContext, ParseOutcome, Parser, Right, SkipBits, Xor,
};
use std::io::{self, BufRead};

#[derive(Clone, Copy)]
struct Atom {
    kind: u8,
    width: u8,
    expected: u64,
}

impl Atom {
    fn from_text(text: &str) -> Self {
        let fields: Vec<_> = text.split(':').collect();
        Self {
            kind: fields[0].parse().unwrap(),
            width: fields[1].parse().unwrap(),
            expected: fields[2].parse().unwrap(),
        }
    }
}

// Normalize C's discarded/unit AST to zero only in this test adapter.
impl<'input> Grammar<'input> for Atom {
    type Output = u64;
}

impl<'input, Backend> Eval<'input, Backend> for Atom {
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<u64> {
        match self.kind {
            1 => Map {
                parser: SkipBits::new(usize::from(self.width)),
                map: |()| 0,
            }
            .eval(backend, input, cursor, context),
            5 => Map {
                parser: Epsilon,
                map: |()| 0,
            }
            .eval(backend, input, cursor, context),
            6 => Fail::<u64>::new().eval(backend, input, cursor, context),
            _ => {
                let literal = Literal::new(self.width, self.expected).unwrap();
                match self.kind {
                    0 => literal.eval(backend, input, cursor, context),
                    2 => Map {
                        parser: And { parser: literal },
                        map: |()| 0,
                    }
                    .eval(backend, input, cursor, context),
                    3 => Right {
                        first: SkipBits::new(3),
                        second: literal,
                    }
                    .eval(backend, input, cursor, context),
                    4 => Left {
                        first: literal,
                        second: SkipBits::new(3),
                    }
                    .eval(backend, input, cursor, context),
                    _ => panic!("unsupported atom"),
                }
            }
        }
    }
}

fn main() {
    for line in io::stdin().lock().lines() {
        let line = line.unwrap();
        let fields: Vec<_> = line.split_whitespace().collect();
        let offset: usize = fields[1].parse().unwrap();
        let cursor = Cursor {
            byte: offset / 8,
            bit: (offset % 8) as u8,
        };
        let first = Atom::from_text(fields[2]);
        let second = Atom::from_text(fields[3]);
        let input: Vec<u8> = if fields[4] == "-" {
            Vec::new()
        } else {
            (0..fields[4].len())
                .step_by(2)
                .map(|i| u8::from_str_radix(&fields[4][i..i + 2], 16).unwrap())
                .collect()
        };
        let result = match fields[0] {
            "0" => ButNot { first, second }.parse(&input, cursor),
            "1" => Difference { first, second }.parse(&input, cursor),
            "2" => Xor { first, second }.parse(&input, cursor),
            _ => panic!("unsupported operation"),
        };
        match result {
            Ok((next, value)) => println!("{} {value}", 8 * next.byte + usize::from(next.bit)),
            Err(_) => println!("error"),
        }
    }
}
