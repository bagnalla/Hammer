//! Minimal reproductions of cleanup discriminant reads after partial enum moves.
//! All four functions translate from promoted MIR with the pinned tools. From
//! elaborated or optimized MIR, the two `partial_*` functions fail in Aeneas;
//! moving the entire variant payload in the `whole_*` functions avoids the read.
#![no_std]

pub fn partial_error<T, E>(input: Result<T, E>) -> Option<T> {
    match input {
        Ok(value) => Some(value),
        Err(_) => None,
    }
}

pub fn whole_error<T, E>(input: Result<T, E>) -> Option<T> {
    match input {
        Ok(value) => Some(value),
        Err(_error) => None,
    }
}

pub fn partial_pair<T>(input: Result<(u8, T), bool>) -> Option<(u8, T)> {
    match input {
        Ok((tag, value)) => Some((tag, value)),
        Err(_) => None,
    }
}

pub fn whole_pair<T>(input: Result<(u8, T), bool>) -> Option<(u8, T)> {
    match input {
        Ok(pair) => {
            let (tag, value) = pair;
            Some((tag, value))
        }
        Err(_) => None,
    }
}
