import RustHammer.ControlSpec

open RustHammer.Code.input_types

open Aeneas Aeneas.Std

namespace RustHammer
open Code

namespace Spec

/-- The empty grammar succeeds at the supplied raw cursor, without consuming input. -/
def epsilon (cursor : Cursor) (outcome : Spec.ParseResult Unit) : Prop :=
  outcome = .Ok (cursor, ())

/-- The failing grammar rejects immediately, for any input. -/
def fail {α : Type} (outcome : Spec.ParseResult α) : Prop :=
  outcome = .Err .Mismatch

/-- A checked conversion follows child success. Conversion errors become grammar
rejection; the callback's error payload never becomes a parser error. -/
def tryMap {α β ε : Type} (child : Cursor → Spec.ParseResult α → Prop)
    (mapping : α → core.result.Result β ε → Prop)
    (cursor : Cursor) (outcome : Spec.ParseResult β) : Prop :=
  ∃ parsed, child cursor parsed ∧ match parsed with
    | .Err error => outcome = .Err error
    | .Ok (next, value) => ∃ mapped, mapping value mapped ∧ match mapped with
      | .Ok converted => outcome = .Ok (next, converted)
      | .Err _ => outcome = .Err .Mismatch

end Spec
end RustHammer
