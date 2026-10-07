import RustHammer.ControlSpec

open RustHammer.Code.grammar.control
  RustHammer.Code.grammar.transform
  RustHammer.Code.input_types

open Aeneas Aeneas.Std

namespace RustHammer.Partial
open Code

/-- Final input keeps the complete result. On partial input, primitive exhaustion
requires more data; all other decoded results and errors stay unchanged. -/
def primitiveResult {α : Type} (status : InputStatus) (result : Spec.ParseResult α) : ParseOutcome α :=
  match status with
  | .Final => Spec.completedResult result
  | .Partial => match result with
    | .Err .UnexpectedEnd => .NeedMore
    | _ => Spec.completedResult result

def primitive {α : Type} (status : InputStatus) (contract : Spec.ParseResult α → Prop)
    (outcome : ParseOutcome α) : Prop :=
  ∃ result, contract result ∧ outcome = primitiveResult status result

/-- Even an empty remaining buffer cannot establish EOF until input is final. -/
def endResult (status : InputStatus) (result : Spec.ParseResult Unit) : ParseOutcome Unit :=
  match result with
  | .Err error => .Error error
  | .Ok (cursor, ()) => match status with
    | .Final => .Success cursor ()
    | .Partial => .NeedMore

def endOutcome (input : Slice U8) (cursor : Cursor) (status : InputStatus)
    (outcome : ParseOutcome Unit) : Prop :=
  ∃ result, Spec.endOutcome input cursor result ∧ outcome = endResult status result

def sequence {α β : Type} (first : Cursor → ParseOutcome α → Prop)
    (second : Cursor → ParseOutcome β → Prop) (cursor : Cursor) (outcome : ParseOutcome (α × β)) : Prop :=
  ∃ left, first cursor left ∧ match left with
    | .NeedMore => outcome = .NeedMore
    | .Error error => outcome = .Error error
    | .Success middle a => ∃ right, second middle right ∧ match right with
      | .NeedMore => outcome = .NeedMore
      | .Error error => outcome = .Error error
      | .Success last b => outcome = .Success last (a, b)

def map {α β : Type} (child : Cursor → ParseOutcome α → Prop) (mapping : α → β → Prop)
    (cursor : Cursor) (outcome : ParseOutcome β) : Prop :=
  ∃ parsed, child cursor parsed ∧ match parsed with
    | .NeedMore => outcome = .NeedMore
    | .Error error => outcome = .Error error
    | .Success next value => ∃ mapped, mapping value mapped ∧ outcome = .Success next mapped

def verify {α : Type} (child : Cursor → ParseOutcome α → Prop) (predicate : α → Prop)
    [DecidablePred predicate] (cursor : Cursor) (outcome : ParseOutcome α) : Prop :=
  ∃ parsed, child cursor parsed ∧ match parsed with
    | .NeedMore => outcome = .NeedMore
    | .Error error => outcome = .Error error
    | .Success next value =>
      if predicate value then outcome = .Success next value else outcome = .Error .Mismatch

/-- Incompleteness of the first alternative does not authorize the second. -/
def choice {α : Type} (first second : Cursor → ParseOutcome α → Prop)
    (cursor : Cursor) (outcome : ParseOutcome α) : Prop :=
  ∃ left, first cursor left ∧ match left with
    | .NeedMore => outcome = .NeedMore
    | .Success next value => outcome = .Success next value
    | .Error error =>
      if Spec.recoverable error then second cursor outcome else outcome = .Error error

def optional {α : Type} (child : Cursor → ParseOutcome α → Prop)
    (cursor : Cursor) (outcome : ParseOutcome (Option α)) : Prop :=
  ∃ parsed, child cursor parsed ∧ match parsed with
    | .NeedMore => outcome = .NeedMore
    | .Success next value => outcome = .Success next (some value)
    | .Error error => if Spec.recoverable error then outcome = .Success cursor none
      else outcome = .Error error

def and {α : Type} (child : Cursor → ParseOutcome α → Prop)
    (cursor : Cursor) (outcome : ParseOutcome Unit) : Prop :=
  ∃ parsed, child cursor parsed ∧ match parsed with
    | .NeedMore => outcome = .NeedMore
    | .Error error => outcome = .Error error
    | .Success _ _ => outcome = .Success cursor ()

def not {α : Type} (child : Cursor → ParseOutcome α → Prop)
    (cursor : Cursor) (outcome : ParseOutcome Unit) : Prop :=
  ∃ parsed, child cursor parsed ∧ match parsed with
    | .NeedMore => outcome = .NeedMore
    | .Success _ _ => outcome = .Error .Mismatch
    | .Error error => if Spec.recoverable error then outcome = .Success cursor ()
      else outcome = .Error error

end RustHammer.Partial
