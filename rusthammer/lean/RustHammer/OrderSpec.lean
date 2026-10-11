import RustHammer.BitsSpec

open RustHammer.Code.input_types

open Aeneas Aeneas.Std

namespace RustHammer.Ordering
open Code

/-- A field is partitioned at physical byte boundaries. -/
def fragmentWidth (start width : Nat) : Nat := min width (8 - start % 8)

/-- Physical fragments retain their ordinary binary significance. Big byte order
weights earlier fragments above later ones; little byte order does the reverse.
All arithmetic is over mathematical naturals, independently of Rust integers. -/
def unsigned (input : Slice U8) (order : ByteOrder) (start width : Nat) : Nat :=
  if width = 0 then 0 else
    let take := fragmentWidth start width
    let part := Spec.unsignedBits input start take
    let tail := unsigned input order (start + take) (width - take)
    match order with
    | .Big => part * 2 ^ (width - take) + tail
    | .Little => part + 2 ^ take * tail
termination_by width
decreasing_by
  have := Nat.mod_lt start (by decide : 0 < 8)
  simp only [fragmentWidth]
  omega

def success (input : Slice U8) (cursor : Cursor) (width : U8) (order : ByteOrder)
    (result : Spec.ParseResult U64) : Prop :=
  ∃ next value, result = .Ok (next, value) ∧ Spec.validCursor input next ∧
    Spec.position next = Spec.position cursor + width.val ∧
    value.val = unsigned input order (Spec.position cursor) width.val

def outcome (input : Slice U8) (cursor : Cursor) (width : U8) (order : ByteOrder)
    (result : Spec.ParseResult U64) : Prop :=
  if Spec.validCursor input cursor then
    if Spec.position cursor + width.val ≤ 8 * input.val.length then
      success input cursor width order result
    else result = .Err .UnexpectedEnd
  else result = .Err .InvalidCursor

abbrev bitSuccess := Spec.bitSuccess
abbrev bitOutcome := Spec.bitOutcome

end RustHammer.Ordering
