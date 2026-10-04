use rusthammer::{parse_flags, Cursor};

fn main() {
    let (next, flags) = parse_flags(&[0b1010_0000], Cursor::start()).unwrap();
    println!("{flags:?}; next cursor: {next:?}");
}
