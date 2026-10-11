//! Minimal pinned-tool regression: Rust passes, generated Lean is ill-typed.
#![no_std]

pub trait Observe {
    type Mark;
    fn begin(&mut self) -> Self::Mark;
}

pub struct Silent;

impl Observe for Silent {
    type Mark = ();
    fn begin(&mut self) {}
}

pub fn generic<O: Observe>(observer: &mut O) -> O::Mark {
    observer.begin()
}

pub fn run() {
    generic(&mut Silent);
}
