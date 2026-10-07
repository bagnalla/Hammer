//! Diagnostic: replaying a sum with two independent borrowed-output lifetimes.
#![no_std]

pub enum Value<'input, 'pattern> {
    Input(&'input [u8]),
    Pattern(&'pattern [u8]),
}

pub fn replay<'input, 'pattern>(value: &Value<'input, 'pattern>) -> Value<'input, 'pattern> {
    match value {
        Value::Input(bytes) => Value::Input(bytes),
        Value::Pattern(bytes) => Value::Pattern(bytes),
    }
}
