import RustHammer.ControlSpec

open RustHammer.Code.input_types

open Aeneas Aeneas.Std

namespace RustHammer
open Code

/-- The second grammar depends on the first value and starts at its successor
cursor. Errors of the first grammar skip the second. -/
def Spec.bind {α β : Type} (first : Cursor → Spec.ParseResult α → Prop)
    (second : α → Cursor → Spec.ParseResult β → Prop) (cursor : Cursor)
    (outcome : Spec.ParseResult β) : Prop :=
  ∃ parsed, first cursor parsed ∧ match parsed with
    | .Err error => outcome = .Err error
    | .Ok (next, value) => second value next outcome

end RustHammer
