import RustHammer.PartialSpec

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

namespace RustHammer.Partial
open Code

/-- Compare matches from the same cursor. First rejection short-circuits; the
second child's recoverable rejection accepts, and its success tests length.
Attempted fatal errors and incompleteness always propagate. -/
def matchRestriction {α β : Type} (allowEqual : Bool)
    (first : Cursor → ParseOutcome α → Prop) (second : Cursor → ParseOutcome β → Prop)
    (cursor : Cursor) (outcome : ParseOutcome α) : Prop :=
  ∃ left, first cursor left ∧ match left with
    | .NeedMore => outcome = .NeedMore
    | .Error error => outcome = .Error error
    | .Success next value => ∃ right, second cursor right ∧ match right with
      | .NeedMore => outcome = .NeedMore
      | .Error error =>
        if Spec.recoverable error then outcome = .Success next value else outcome = .Error error
      | .Success other _ =>
        if Spec.matchEndpointOrder allowEqual next other then outcome = .Success next value
        else outcome = .Error .Mismatch

/-- Exactly one success accepts; a second recoverable rejection after the first
one becomes the reported error. Incompleteness is not evidence of rejection. -/
def exclusive {α : Type} (first second : Cursor → ParseOutcome α → Prop)
    (cursor : Cursor) (outcome : ParseOutcome α) : Prop :=
  ∃ left, first cursor left ∧ match left with
    | .NeedMore => outcome = .NeedMore
    | .Error error =>
      if Spec.recoverable error then second cursor outcome else outcome = .Error error
    | .Success next value => ∃ right, second cursor right ∧ match right with
      | .NeedMore => outcome = .NeedMore
      | .Success _ _ => outcome = .Error .Mismatch
      | .Error error =>
        if Spec.recoverable error then outcome = .Success next value else outcome = .Error error

end RustHammer.Partial

namespace RustHammer.Spec
open Code

def matchRestriction {α β : Type} (allowEqual : Bool)
    (first : Cursor → ParseResult α → Prop) (second : Cursor → ParseResult β → Prop)
    (cursor : Cursor) (result : ParseResult α) : Prop :=
  Partial.matchRestriction allowEqual (fun start => completed (first start))
    (fun start => completed (second start)) cursor (completedResult result)

def exclusive {α : Type} (first second : Cursor → ParseResult α → Prop)
    (cursor : Cursor) (result : ParseResult α) : Prop :=
  Partial.exclusive (fun start => completed (first start)) (fun start => completed (second start))
    cursor (completedResult result)

end RustHammer.Spec
