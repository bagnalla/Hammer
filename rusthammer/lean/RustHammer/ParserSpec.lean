import RustHammer.ControlSpec

open RustHammer.Code.grammar.control
  RustHammer.Code.grammar.transform
  RustHammer.Code.input_types

open Aeneas Aeneas.Std

namespace RustHammer.Contracts
open Code

def primitive {α : Type} (contract : Spec.ParseResult α → Prop)
    (outcome : Spec.ParseResult α) : Prop :=
  ∃ result, contract result ∧ outcome = result

def endOutcome (input : Slice U8) (cursor : Cursor)
    (outcome : Spec.ParseResult Unit) : Prop :=
  ∃ result, Spec.endOutcome input cursor result ∧ outcome = result

def sequence {α β : Type} (first : Cursor → Spec.ParseResult α → Prop)
    (second : Cursor → Spec.ParseResult β → Prop) (cursor : Cursor) (outcome : Spec.ParseResult (α × β)) : Prop :=
  ∃ left, first cursor left ∧ match left with
    | .Err error => outcome = .Err error
    | .Ok (middle, a) => ∃ right, second middle right ∧ match right with
      | .Err error => outcome = .Err error
      | .Ok (last, b) => outcome = .Ok (last, (a, b))

def map {α β : Type} (child : Cursor → Spec.ParseResult α → Prop) (mapping : α → β → Prop)
    (cursor : Cursor) (outcome : Spec.ParseResult β) : Prop :=
  ∃ parsed, child cursor parsed ∧ match parsed with
    | .Err error => outcome = .Err error
    | .Ok (next, value) => ∃ mapped, mapping value mapped ∧ outcome = .Ok (next, mapped)

def verify {α : Type} (child : Cursor → Spec.ParseResult α → Prop) (predicate : α → Prop)
    [DecidablePred predicate] (cursor : Cursor) (outcome : Spec.ParseResult α) : Prop :=
  ∃ parsed, child cursor parsed ∧ match parsed with
    | .Err error => outcome = .Err error
    | .Ok (next, value) =>
      if predicate value then outcome = .Ok (next, value) else outcome = .Err .Mismatch

/-- Recoverable rejection selects the second alternative at the original cursor. -/
def choice {α : Type} (first second : Cursor → Spec.ParseResult α → Prop)
    (cursor : Cursor) (outcome : Spec.ParseResult α) : Prop :=
  ∃ left, first cursor left ∧ match left with
    | .Ok (next, value) => outcome = .Ok (next, value)
    | .Err error =>
      if Spec.recoverable error then second cursor outcome else outcome = .Err error

def optional {α : Type} (child : Cursor → Spec.ParseResult α → Prop)
    (cursor : Cursor) (outcome : Spec.ParseResult (Option α)) : Prop :=
  ∃ parsed, child cursor parsed ∧ match parsed with
    | .Ok (next, value) => outcome = .Ok (next, (some value))
    | .Err error => if Spec.recoverable error then outcome = .Ok (cursor, none)
      else outcome = .Err error

def and {α : Type} (child : Cursor → Spec.ParseResult α → Prop)
    (cursor : Cursor) (outcome : Spec.ParseResult Unit) : Prop :=
  ∃ parsed, child cursor parsed ∧ match parsed with
    | .Err error => outcome = .Err error
    | .Ok (_, _) => outcome = .Ok (cursor, ())

def not {α : Type} (child : Cursor → Spec.ParseResult α → Prop)
    (cursor : Cursor) (outcome : Spec.ParseResult Unit) : Prop :=
  ∃ parsed, child cursor parsed ∧ match parsed with
    | .Ok (_, _) => outcome = .Err .Mismatch
    | .Err error => if Spec.recoverable error then outcome = .Ok (cursor, ())
      else outcome = .Err error

end RustHammer.Contracts
