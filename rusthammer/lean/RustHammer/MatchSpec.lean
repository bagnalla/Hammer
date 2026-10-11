import RustHammer.ParserSpec

open RustHammer.Code.input_types

open Aeneas Aeneas.Std

namespace RustHammer.Spec
open Code

/-- Lexicographic order on mathematical byte/bit coordinates. For normalized
endpoints this agrees with absolute bit-position order, even beyond usize. -/
abbrev matchEndpointOrder (allowEqual : Bool) (first second : Cursor) : Prop :=
  second.byte.val < first.byte.val ∨
    (second.byte.val = first.byte.val ∧
      if allowEqual then second.bit.val ≤ first.bit.val else second.bit.val < first.bit.val)

end RustHammer.Spec

namespace RustHammer.Contracts
open Code

/-- Compare matches from the same cursor. First rejection short-circuits; the
second child's recoverable rejection accepts, and its success tests length.
Attempted fatal errors always propagate. -/
def matchRestriction {α β : Type} (allowEqual : Bool)
    (first : Cursor → Spec.ParseResult α → Prop) (second : Cursor → Spec.ParseResult β → Prop)
    (cursor : Cursor) (outcome : Spec.ParseResult α) : Prop :=
  ∃ left, first cursor left ∧ match left with
    | .Err error => outcome = .Err error
    | .Ok (next, value) => ∃ right, second cursor right ∧ match right with
      | .Err error =>
        if Spec.recoverable error then outcome = .Ok (next, value) else outcome = .Err error
      | .Ok (other, _) =>
        if Spec.matchEndpointOrder allowEqual next other then outcome = .Ok (next, value)
        else outcome = .Err .Mismatch

/-- Exactly one success accepts; a second recoverable rejection after the first
one becomes the reported error. Incompleteness is not evidence of rejection. -/
def exclusive {α : Type} (first second : Cursor → Spec.ParseResult α → Prop)
    (cursor : Cursor) (outcome : Spec.ParseResult α) : Prop :=
  ∃ left, first cursor left ∧ match left with
    | .Err error =>
      if Spec.recoverable error then second cursor outcome else outcome = .Err error
    | .Ok (next, value) => ∃ right, second cursor right ∧ match right with
      | .Ok (_, _) => outcome = .Err .Mismatch
      | .Err error =>
        if Spec.recoverable error then outcome = .Ok (next, value) else outcome = .Err error

end RustHammer.Contracts

namespace RustHammer.Spec
open Code

def matchRestriction {α β : Type} (allowEqual : Bool)
    (first : Cursor → ParseResult α → Prop) (second : Cursor → ParseResult β → Prop)
    (cursor : Cursor) (result : ParseResult α) : Prop :=
  Contracts.matchRestriction allowEqual (fun start => satisfies (first start))
    (fun start => satisfies (second start)) cursor (result)

def exclusive {α : Type} (first second : Cursor → ParseResult α → Prop)
    (cursor : Cursor) (result : ParseResult α) : Prop :=
  Contracts.exclusive (fun start => satisfies (first start)) (fun start => satisfies (second start))
    cursor (result)

end RustHammer.Spec
