// Text protocol for the optional C differential check. Not extracted to Lean.
fn main() {
    use std::io::{self, BufRead, Write};
    fn order(flags: u8) -> Order {
        Order {
            bit: if flags & 2 != 0 {
                BitOrder::HighFirst
            } else {
                BitOrder::LowFirst
            },
            byte: if flags & 1 != 0 {
                ByteOrder::Big
            } else {
                ByteOrder::Little
            },
        }
    }
    let mut out = io::BufWriter::new(io::stdout().lock());
    for line in io::stdin().lock().lines() {
        let line = line.unwrap();
        let words: Vec<_> = line.split_whitespace().collect();
        let input: Vec<u8> = if words[1] == "-" {
            Vec::new()
        } else {
            words[1]
                .as_bytes()
                .chunks_exact(2)
                .map(|p| u8::from_str_radix(std::str::from_utf8(p).unwrap(), 16).unwrap())
                .collect()
        };
        let args: Vec<usize> = words[2..].iter().map(|p| p.parse().unwrap()).collect();
        let result = match words[0] {
            "R" | "S" => {
                let cursor = Cursor::new(args[0], args[1] as u8, args[2] as u8).unwrap();
                let ctx = Context {
                    order: order(args[3] as u8),
                    status: InputStatus::Final,
                };
                let parsed = if words[0] == "R" {
                    Field::new(args[4] as u8)
                        .unwrap()
                        .parse_with(&input, cursor, ctx)
                } else {
                    match skip_bits(&input, cursor, args[4], ctx) {
                        Outcome::Success(end, ()) => Outcome::Success(end, 0),
                        Outcome::Error(error) => Outcome::Error(error),
                        Outcome::NeedMore => Outcome::NeedMore,
                    }
                };
                match parsed {
                    Outcome::Success(c, value) => {
                        format!("1 {} {} {} {value}", c.byte, c.high, c.low)
                    }
                    _ => "0".into(),
                }
            }
            "N" => {
                let ctx = Context {
                    order: order(args[0] as u8),
                    status: InputStatus::Final,
                };
                let widths = [
                    args[3] as u8,
                    args[4] as u8,
                    args[5] as u8,
                    args[6] as u8,
                    args[7] as u8,
                ];
                match nested(
                    &input,
                    widths,
                    order(args[1] as u8),
                    order(args[2] as u8),
                    ctx,
                )
                .unwrap()
                {
                    Outcome::Success(end, ((a, (b, (c, d)), e), _)) => {
                        let rank = 8 * end.byte + end.high as usize + end.low as usize;
                        format!("1 {rank} {a} {b} {c} {d} {e}")
                    }
                    _ => "0".into(),
                }
            }
            _ => panic!("unknown request"),
        };
        writeln!(out, "{result}").unwrap();
    }
}
