import RustHammer.PartialSpec
import RustHammer.RecordSpec

open Aeneas Aeneas.Std

namespace RustHammer.Partial
open Code
open record_example

/-- The ordered marker grammar, with finality applied at each primitive. -/
def markerOutcome (input : Slice U8) (cursor : Cursor) (status : InputStatus)
    (outcome : ParseOutcome U64) : Prop :=
  map (sequence
    (choice (fun start => primitive status (Spec.literalOutcome input start 16#u8 51966#u64))
      (fun start => primitive status (Spec.literalOutcome input start 8#u8 202#u64)))
    (fun start => endOutcome input start status))
    (fun fields value => value = fields.1) cursor outcome

/-- An aligned payload on partial input waits for bytes or confirmation of EOF.
A declared payload shorter than the available suffix is already a rejection. -/
def recordBodyOutcome (input : Slice U8) (cursor : Cursor) (count : Usize)
    (outcome : ParseOutcome Record) : Prop :=
  if cursor.byte.val + count.val < input.val.length then outcome = .Error .TrailingInput
  else outcome = .NeedMore

/-- Independent partial-input format contract. Even a full valid record awaits
EOF because this format requires exact consumption. Decoding uses the same
natural-number field specification as the complete-input contract. -/
def recordOutcome (input : Slice U8) (cursor : Cursor) (outcome : ParseOutcome Record) : Prop :=
  if Spec.validCursor input cursor then
    if cursor.bit.val = 0 then
      if cursor.byte.val + 3 ≤ input.val.length then
        if Spec.recordVersion input cursor = 1 ∧ Spec.recordLength input cursor ≤ 1024 then
          if cursor.byte.val + 3 + Spec.recordLength input cursor < input.val.length then
            outcome = .Error .TrailingInput
          else outcome = .NeedMore
        else outcome = .Error .Mismatch
      else outcome = .NeedMore
    else outcome = .Error .Unaligned
  else outcome = .Error .InvalidCursor

end RustHammer.Partial
