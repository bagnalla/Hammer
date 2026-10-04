use rusthammer::{parse_marker, ConfigError, Cursor, Marker};

fn main() -> Result<(), ConfigError> {
    let parser = Marker::new()?;
    for input in [&[0xca, 0xfe][..], &[0xca][..], &[0xca, 0xfe, 0][..]] {
        println!(
            "{input:02x?}: {:?}",
            parse_marker(input, Cursor::start(), &parser)
        );
    }
    Ok(())
}
