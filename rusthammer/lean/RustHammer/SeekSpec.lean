import RustHammer.PositionSpec

open Aeneas Aeneas.Std
open RustHammer.Code.input_types RustHammer.Code.grammar.position

namespace RustHammer.Seeking
open Code

/-- The only construction constraint is normalization of absolute destinations. -/
def valid (parser : Seek) : Prop :=
  match parser.target with
  | .Absolute target => target.bit.val < 8
  | .Relative _ | .End _ => True

/-- Backward movement uses a mathematical count, independently of the byte/bit
subtraction algorithm and without truncating a negative displacement. -/
def retreatOutcome (length : Nat) (cursor : Cursor) (bits : Nat)
    (result : core.result.Result Cursor ParseError) : Prop :=
  if Spec.validPosition length cursor then
    if bits ≤ Spec.position cursor then
      ∃ next, result = .Ok next ∧ Spec.validPosition length next ∧
        Spec.position next + bits = Spec.position cursor
    else result = .Err .Mismatch
  else result = .Err .InvalidCursor

/-- A destination is an unbounded signed position. Entry validation precedes
underflow and exhaustion; success gives its unique normalized in-bounds cursor. -/
def targetOutcome (length : Nat) (cursor : Cursor) (destination : Int)
    (result : core.result.Result Cursor ParseError) : Prop :=
  if Spec.validPosition length cursor then
    if destination < 0 then result = .Err .Mismatch
    else if (8 * length : Nat) < destination then result = .Err .UnexpectedEnd
    else ∃ next, result = .Ok next ∧ Spec.validPosition length next ∧
      (Spec.position next : Int) = destination
  else result = .Err .InvalidCursor

def targetPosition (target : SeekTarget) (length : Nat) (cursor : Cursor) : Int :=
  match target with
  | .Absolute target => Spec.position target
  | .Relative offset => (Spec.position cursor : Int) + offset.val
  | .End offset => (8 * length : Nat) + offset.val

def awaitsEnd (target : SeekTarget) (status : InputStatus) : Prop :=
  match target, status with
  | .End _, .Partial => True
  | _, _ => False

instance (target : SeekTarget) (status : InputStatus) : Decidable (awaitsEnd target status) := by
  cases target <;> cases status <;> unfold awaitsEnd <;> infer_instance

def reported (result : core.result.Result Cursor ParseError) : Spec.ParseResult Cursor :=
  match result with
  | .Ok next => .Ok (next, next)
  | .Err error => .Err error

/-- The complete seek contract. The destination is also the output; finality
affects only end-relative evaluation and classification of unavailable input. -/
def outcome (parser : Seek) (length : Nat) (cursor : Cursor) (status : InputStatus)
    (result : ParseOutcome Cursor) : Prop :=
  if Spec.validPosition length cursor then
    if awaitsEnd parser.target status then result = .NeedMore
    else ∃ raw, targetOutcome length cursor (targetPosition parser.target length cursor) raw ∧
      result = Partial.primitiveResult status (reported raw)
  else result = .Error .InvalidCursor

end RustHammer.Seeking
