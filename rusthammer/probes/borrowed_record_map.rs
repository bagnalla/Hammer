//! Extraction probe: a capturing `Fn` constructs a struct containing its borrowed input.
#![no_std]

pub struct BorrowedRecord<'input> {
    pub version: u64,
    pub payload: &'input [u8],
}

pub fn apply<A, B, F: Fn(A) -> B>(callback: F, value: A) -> B {
    callback(value)
}

pub fn borrowed_record<'input>(input: &'input [u8], version: u64) -> BorrowedRecord<'input> {
    apply(
        move |payload: &'input [u8]| BorrowedRecord { version, payload },
        input,
    )
}
