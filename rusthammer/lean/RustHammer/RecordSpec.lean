import RustHammer.ControlSpec

open Aeneas Aeneas.Std

namespace RustHammer.Spec
open Code

/-- The private record configuration fixes the three field widths. -/
def recordParser : RecordParser :=
  { version := { width := 3#u8 }, flags := { width := 5#u8 }, length := { width := 16#u8 } }

abbrev validRecordParser (parser : RecordParser) : Prop := parser = recordParser

abbrev HeaderFields := U64 × (U64 × U64)

/-- Keep field decoders folded during control-flow proofs; decoding lemmas unfold them explicitly. -/
@[irreducible] def recordVersion (input : Slice U8) (cursor : Cursor) : Nat :=
  unsignedBits input (position cursor) 3

@[irreducible] def recordFlags (input : Slice U8) (cursor : Cursor) : Nat :=
  unsignedBits input (position cursor + 3) 5

@[irreducible] def recordLength (input : Slice U8) (cursor : Cursor) : Nat :=
  unsignedBits input (position cursor + 8) 16

/-- A full aligned header is three bytes; field values use positional binary notation. -/
def recordHeaderSuccess (input : Slice U8) (cursor : Cursor)
    (result : ParseResult HeaderFields) : Prop :=
  ∃ next version flags length, result = .Ok (next, (version, (flags, length))) ∧
    validCursor input next ∧ next.byte.val = cursor.byte.val + 3 ∧ next.bit.val = 0 ∧
    version.val = recordVersion input cursor ∧ flags.val = recordFlags input cursor ∧
    length.val = recordLength input cursor

def recordHeaderOutcome (input : Slice U8) (cursor : Cursor)
    (result : ParseResult HeaderFields) : Prop :=
  if cursor.byte.val + 3 ≤ input.val.length then recordHeaderSuccess input cursor result
  else result = .Err .UnexpectedEnd

abbrev recordHeaderAllowed (fields : HeaderFields) : Prop :=
  fields.1.val = 1 ∧ fields.2.2.val ≤ 1024

/-- The decoded payload is the declared subsequence, and the record consumes the suffix. -/
def recordSuccess (input : Slice U8) (cursor : Cursor) (result : ParseResult Record) : Prop :=
  ∃ next record, result = .Ok (next, record) ∧
    next.byte.val = input.val.length ∧ next.bit.val = 0 ∧
    record.version.val = recordVersion input cursor ∧
    record.flags.val = recordFlags input cursor ∧
    record.payload.val = (input.val.drop (cursor.byte.val + 3)).take (recordLength input cursor)

/-- The payload stage preserves header values and consumes exactly the requested suffix. -/
def recordBodySuccess (input : Slice U8) (cursor : Cursor) (version flags : U64) (count : Usize)
    (result : ParseResult Record) : Prop :=
  ∃ next record, result = .Ok (next, record) ∧
    next.byte.val = input.val.length ∧ next.bit.val = 0 ∧
    record.version = version ∧ record.flags = flags ∧
    record.payload.val = (input.val.drop cursor.byte.val).take count.val

def recordBodyOutcome (input : Slice U8) (cursor : Cursor) (version flags : U64) (count : Usize)
    (result : ParseResult Record) : Prop :=
  if cursor.byte.val + count.val ≤ input.val.length then
    if cursor.byte.val + count.val = input.val.length then
      recordBodySuccess input cursor version flags count result
    else result = .Err .TrailingInput
  else result = .Err .UnexpectedEnd

/-- Independent complete-buffer format contract, including the order of rejections.
All bounds and decoded lengths use natural numbers, not machine arithmetic. -/
def recordOutcome (input : Slice U8) (cursor : Cursor) (result : ParseResult Record) : Prop :=
  if validCursor input cursor then
    if cursor.bit.val = 0 then
      if cursor.byte.val + 3 ≤ input.val.length then
        if recordVersion input cursor = 1 ∧ recordLength input cursor ≤ 1024 then
          if cursor.byte.val + 3 + recordLength input cursor ≤ input.val.length then
            if cursor.byte.val + 3 + recordLength input cursor = input.val.length then
              recordSuccess input cursor result
            else result = .Err .TrailingInput
          else result = .Err .UnexpectedEnd
        else result = .Err .Mismatch
      else result = .Err .UnexpectedEnd
    else result = .Err .Unaligned
  else result = .Err .InvalidCursor

end RustHammer.Spec
