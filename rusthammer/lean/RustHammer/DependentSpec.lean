import RustHammer.BindSpec
import RustHammer.RepeatSpec

open RustHammer.Code.input_types

open Aeneas Aeneas.Std

namespace RustHammer.Spec
open Code

/-- The format's count byte is positional binary, independent of its parser. -/
def countValue (input : Slice U8) (cursor : Cursor) : Nat :=
  unsignedBits input (position cursor) 8

/-- Decode an eight-bit count, rejecting values over the format limit before
parsing a body. Truncation reports UnexpectedEnd, even at unaligned starts. -/
def countPrefix (input : Slice U8) (cursor : Cursor)
    (outcome : Spec.ParseResult Usize) : Prop :=
  if validCursor input cursor then
    if position cursor + 8 ≤ 8 * input.val.length then
      if countValue input cursor ≤ 64 then
        ∃ next count, outcome = .Ok (next, count) ∧ validCursor input next ∧
          position next = position cursor + 8 ∧ count.val = countValue input cursor
      else outcome = .Err .Mismatch
    else outcome = (.Err .UnexpectedEnd)
  else outcome = .Err .InvalidCursor

/-- The byte format consists of the count field followed by exactly that many
aligned bytes. The payload is a slice of the original input; trailing input is
permitted. Alignment is checked only after successful count decoding. -/
def dependentPayload (input : Slice U8) (cursor : Cursor)
    (outcome : Spec.ParseResult (Slice U8)) : Prop :=
  Contracts.bind (fun start => countPrefix input start)
    (fun count start => Contracts.primitive (takeAlignedOutcome input start count)) cursor outcome

/-- The element format instead contains `count` four-bit numbers, in order.
Natural-number count and bit positions specify exact consumption and values. -/
def dependentFields (input : Slice U8) (cursor : Cursor)
    (outcome : Spec.ParseResult (alloc.vec.Vec U64)) : Prop :=
  Contracts.bind (fun start => countPrefix input start)
    (fun count start => repeatN
      (fun pos => Contracts.primitive (bitsOutcome input pos 4#u8)) count.val start) cursor outcome

end RustHammer.Spec
