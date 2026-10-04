import RustHammer.PartialSpec

open Aeneas Aeneas.Std

namespace RustHammer
open Code

/-- The second grammar depends on the first value and starts at its successor
cursor. Errors and incompleteness of the first grammar skip the second. -/
def Partial.bind {α β : Type} (first : Cursor → ParseOutcome α → Prop)
    (second : α → Cursor → ParseOutcome β → Prop) (cursor : Cursor)
    (outcome : ParseOutcome β) : Prop :=
  ∃ parsed, first cursor parsed ∧ match parsed with
    | .NeedMore => outcome = .NeedMore
    | .Error error => outcome = .Error error
    | .Success next value => second value next outcome

def Spec.bind {α β : Type} (first : Cursor → Spec.ParseResult α → Prop)
    (second : α → Cursor → Spec.ParseResult β → Prop) (cursor : Cursor)
    (result : Spec.ParseResult β) : Prop :=
  ∃ parsed, first cursor parsed ∧ match parsed with
    | .Err error => result = .Err error
    | .Ok (next, value) => second value next result

end RustHammer
