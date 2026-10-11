import RustHammer.ParserSpec

open RustHammer.Code.input_types

open Aeneas Aeneas.Std

namespace RustHammer
open Code

namespace Contracts

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

end Contracts

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
