import RustHammer.PartialSpec

open RustHammer.Code.grammar.numeric
  RustHammer.Code.input_types

open Aeneas Aeneas.Std

namespace RustHammer.Spec
open Code

abbrev validSignedBits (parser : SignedBits) : Prop := validBits parser.bits

def signedBitsNewOutcome (width : U8) (result : core.result.Result SignedBits ConfigError) : Prop :=
  if width.val ≤ 64 then result = .Ok { bits := { width } }
  else result = .Err .InvalidWidth

/-- Mathematical two's-complement interpretation, using unbounded integers.
The empty field is defined as zero; otherwise the top bit has negative weight. -/
def signedValue (width value : Nat) : Int :=
  if width = 0 then 0
  else if value < 2 ^ (width - 1) then value else (value : Int) - (2 ^ width : Nat)

def signedBitsSuccess (input : Slice U8) (cursor : Cursor) (width : U8)
    (result : ParseResult I64) : Prop :=
  ∃ next value, result = .Ok (next, value) ∧ validCursor input next ∧
    position next = position cursor + width.val ∧
    value.val = signedValue width.val (unsignedBits input (position cursor) width.val)

/-- Cursor validation precedes decoding even at width zero. Signedness changes
the decoded value, not consumption or the classification of missing input. -/
def signedBitsOutcome (input : Slice U8) (cursor : Cursor) (width : U8)
    (result : ParseResult I64) : Prop :=
  if validCursor input cursor then
    if position cursor + width.val ≤ 8 * input.val.length then
      signedBitsSuccess input cursor width result
    else result = .Err .UnexpectedEnd
  else result = .Err .InvalidCursor

end RustHammer.Spec
