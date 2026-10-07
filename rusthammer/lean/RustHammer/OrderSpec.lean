import RustHammer.BitsSpec

open RustHammer.Code.input_types

open Aeneas Aeneas.Std

namespace RustHammer.Ordering
open Code

/-- A field is partitioned at physical byte boundaries. -/
def fragmentWidth (start width : Nat) : Nat := min width (8 - start % 8)

/-- Convert a consumed-bit count into the fragment's high-first physical index. -/
def fragmentStart (order : BitOrder) (start take : Nat) : Nat :=
  8 * (start / 8) + match order with
    | .HighFirst => start % 8
    | .LowFirst => 8 - start % 8 - take

/-- Physical fragments retain their ordinary binary significance. Big byte order
weights earlier fragments above later ones; little byte order does the reverse.
All arithmetic is over mathematical naturals, independently of Rust integers. -/
def unsigned (input : Slice U8) (order : Order) (start width : Nat) : Nat :=
  if width = 0 then 0 else
    let take := fragmentWidth start width
    let part := Spec.unsignedBits input (fragmentStart order.bit start take) take
    let tail := unsigned input order (start + take) (width - take)
    match order.byte with
    | .Big => part * 2 ^ (width - take) + tail
    | .Little => part + 2 ^ take * tail
termination_by width
decreasing_by
  have := Nat.mod_lt start (by decide : 0 < 8)
  simp only [fragmentWidth]
  omega

def success (input : Slice U8) (cursor : Cursor) (width : U8) (order : Order)
    (result : Spec.ParseResult U64) : Prop :=
  ∃ next value, result = .Ok (next, value) ∧ Spec.validCursor input next ∧
    Spec.position next = Spec.position cursor + width.val ∧
    value.val = unsigned input order (Spec.position cursor) width.val

def outcome (input : Slice U8) (cursor : Cursor) (width : U8) (order : Order)
    (result : Spec.ParseResult U64) : Prop :=
  if Spec.validCursor input cursor then
    if Spec.position cursor + width.val ≤ 8 * input.val.length then
      success input cursor width order result
    else result = .Err .UnexpectedEnd
  else result = .Err .InvalidCursor

def bitSuccess (input : Slice U8) (cursor : Cursor) (order : BitOrder)
    (result : Spec.ParseResult Bool) : Prop :=
  ∃ next value, result = .Ok (next, value) ∧
    next.byte.val = cursor.byte.val + (if cursor.bit.val = 7 then 1 else 0) ∧
    next.bit.val = (cursor.bit.val + 1) % 8 ∧
    value = (input.val[cursor.byte.val]!).val.testBit
      (match order with | .HighFirst => 7 - cursor.bit.val | .LowFirst => cursor.bit.val)

def bitOutcome (input : Slice U8) (cursor : Cursor) (order : BitOrder)
    (result : Spec.ParseResult Bool) : Prop :=
  if cursor.bit.val < 8 ∧ cursor.byte.val < input.val.length then
    bitSuccess input cursor order result
  else result = .Err
    (if cursor.bit.val < 8 ∧ cursor.byte.val = input.val.length ∧ cursor.bit.val = 0
     then ParseError.UnexpectedEnd else ParseError.InvalidCursor)

end RustHammer.Ordering
