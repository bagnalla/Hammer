import RustHammer.Spec

open Aeneas Aeneas.Std

namespace RustHammer.Spec
open Code

/-- The numeric parser's private configuration invariant. -/
abbrev validBits (parser : Bits) : Prop := parser.width.val ≤ 64

/-- Construction checks the width without inspecting any input. -/
def bitsNewOutcome (width : U8) (result : core.result.Result Bits ConfigError) : Prop :=
  if width.val ≤ 64 then result = .Ok { width }
  else result = .Err .InvalidWidth

/-- A normalized cursor is in the input or exactly at its end. -/
abbrev validCursor (input : Slice U8) (cursor : Cursor) : Prop :=
  cursor.bit.val < 8 ∧ position cursor ≤ 8 * input.val.length

/-- The bit at an absolute position, interpreted as a natural-number digit. -/
def bitAt (input : Slice U8) (pos : Nat) : Nat :=
  if (input.val[pos / 8]!).val.testBit (7 - pos % 8) then 1 else 0

/-- Positional binary notation, independent of machine arithmetic and parser control flow. -/
def unsignedBits (input : Slice U8) (start : Nat) : Nat → Nat
  | 0 => 0
  | width + 1 => bitAt input start * 2 ^ width + unsignedBits input (start + 1) width

/-- A numeric field returns its binary value and consumes exactly its width. -/
def bitsSuccess (input : Slice U8) (cursor : Cursor) (width : U8)
    (result : ParseResult U64) : Prop :=
  ∃ next value, result = .Ok (next, value) ∧ validCursor input next ∧
    position next = position cursor + width.val ∧
    value.val = unsignedBits input (position cursor) width.val

/-- For a validated width, zero-width fields succeed at every valid cursor,
including end-of-input. Cursor and input checks still happen on every parse. -/
def bitsOutcome (input : Slice U8) (cursor : Cursor) (width : U8)
    (result : ParseResult U64) : Prop :=
  if validCursor input cursor then
    if position cursor + width.val ≤ 8 * input.val.length then
      bitsSuccess input cursor width result
    else result = .Err ParseError.UnexpectedEnd
  else result = .Err ParseError.InvalidCursor

end RustHammer.Spec
