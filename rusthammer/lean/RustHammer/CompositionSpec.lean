import RustHammer.PartialSpec

open Aeneas Aeneas.Std

namespace RustHammer
open Code

namespace Partial

/-- The empty grammar succeeds at the supplied raw cursor, in either input mode. -/
def epsilon (cursor : Cursor) (outcome : ParseOutcome Unit) : Prop :=
  outcome = .Success cursor ()

/-- The failing grammar rejects immediately, regardless of input finality. -/
def fail {α : Type} (outcome : ParseOutcome α) : Prop :=
  outcome = .Error .Mismatch

/-- A checked conversion follows child success. Conversion errors become grammar
rejection; the callback's error payload never becomes a parser error. -/
def tryMap {α β ε : Type} (child : Cursor → ParseOutcome α → Prop)
    (mapping : α → core.result.Result β ε → Prop)
    (cursor : Cursor) (outcome : ParseOutcome β) : Prop :=
  ∃ parsed, child cursor parsed ∧ match parsed with
    | .NeedMore => outcome = .NeedMore
    | .Error error => outcome = .Error error
    | .Success next value => ∃ mapped, mapping value mapped ∧ match mapped with
      | .Ok converted => outcome = .Success next converted
      | .Err _ => outcome = .Error .Mismatch

end Partial

namespace Spec

def epsilon (cursor : Cursor) (result : ParseResult Unit) : Prop :=
  result = .Ok (cursor, ())

def fail {α : Type} (result : ParseResult α) : Prop :=
  result = .Err .Mismatch

def tryMap {α β ε : Type} (child : Cursor → ParseResult α → Prop)
    (mapping : α → core.result.Result β ε → Prop)
    (cursor : Cursor) (result : ParseResult β) : Prop :=
  ∃ parsed, child cursor parsed ∧ match parsed with
    | .Err error => result = .Err error
    | .Ok (next, value) => ∃ mapped, mapping value mapped ∧ match mapped with
      | .Ok converted => result = .Ok (next, converted)
      | .Err _ => result = .Err .Mismatch

end Spec
end RustHammer
