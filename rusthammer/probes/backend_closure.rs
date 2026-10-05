//! Pinned Aeneas diagnostic: an unused backend type on a zero-capture closure
//! inside a lifetime-generic evaluator can leave Lean unable to infer that type.
//! `generic` reproduces the failure; `fixed` constructs the closure separately.
#![no_std]

fn apply<F: Fn(u64) -> u64>(callback: &F, value: u64) -> u64 {
    callback(value)
}

pub trait Eval<'input, Backend> {
    fn eval(&self, backend: &mut Backend, value: &'input u64) -> u64;
}

pub struct Generic;
impl<'input, Backend> Eval<'input, Backend> for Generic {
    fn eval(&self, _backend: &mut Backend, value: &'input u64) -> u64 {
        apply(&|v| v, *value)
    }
}

fn identity() -> impl Fn(u64) -> u64 {
    |v| v
}

pub struct Fixed;
impl<'input, Backend> Eval<'input, Backend> for Fixed {
    fn eval(&self, _backend: &mut Backend, value: &'input u64) -> u64 {
        apply(&identity(), *value)
    }
}

pub fn generic<Backend>(backend: &mut Backend, value: u64) -> u64 {
    Generic.eval(backend, &value)
}

pub fn fixed<Backend>(backend: &mut Backend, value: u64) -> u64 {
    Fixed.eval(backend, &value)
}
