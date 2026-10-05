#[path = "support/marker.rs"]
mod marker_example;

use marker_example::{parse_marker, Marker};
use rusthammer::{ConfigError, Cursor};

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
