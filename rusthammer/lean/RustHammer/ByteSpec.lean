import RustHammer.PartialSpec

open RustHammer.Code.input_types

open Aeneas Aeneas.Std

namespace RustHammer.Spec
open Code

/-- Eight bits interpreted as positional binary, with a byte-sized output. -/
def byteSuccess (input : Slice U8) (cursor : Cursor) (result : ParseResult U8) : Prop :=
  ∃ next value, result = .Ok (next, value) ∧ validCursor input next ∧
    position next = position cursor + 8 ∧
    value.val = unsignedBits input (position cursor) 8

def byteOutcome (input : Slice U8) (cursor : Cursor) (result : ParseResult U8) : Prop :=
  if validCursor input cursor then
    if position cursor + 8 ≤ 8 * input.val.length then byteSuccess input cursor result
    else result = .Err .UnexpectedEnd
  else result = .Err .InvalidCursor

/-- Match a mathematical list of bytes in order. Each byte denotes eight bits,
including at unaligned positions. A fully decoded mismatch rejects immediately;
an incomplete byte is governed by input finality. The empty list is the identity,
including for raw cursors. This definition uses no machine counter or indexing. -/
def matchBytes (input : Slice U8) (status : InputStatus) :
    List U8 → Cursor → ParseOutcome Unit → Prop
  | [], cursor, outcome => outcome = .Success cursor ()
  | expected :: rest, cursor, outcome =>
    ∃ decoded, Partial.primitive status (byteOutcome input cursor) decoded ∧
      match decoded with
      | .Success next value => if value = expected then matchBytes input status rest next outcome
          else outcome = .Error .Mismatch
      | .Error error => outcome = .Error error
      | .NeedMore => outcome = .NeedMore

/-- Successful output is the configured pattern, independently of the input's
storage. Slice identity is checked by Rust tests; the Lean slice model is by value. -/
def bytePatternOutcome (input : Slice U8) (status : InputStatus) (pattern : Slice U8)
    (cursor : Cursor) (outcome : ParseOutcome (Slice U8)) : Prop :=
  match outcome with
  | .Success next output => output = pattern ∧ matchBytes input status pattern.val cursor (.Success next ())
  | .Error error => matchBytes input status pattern.val cursor (.Error error)
  | .NeedMore => matchBytes input status pattern.val cursor .NeedMore

def bytePatternComplete (input pattern : Slice U8) (cursor : Cursor)
    (result : ParseResult (Slice U8)) : Prop :=
  bytePatternOutcome input .Final pattern cursor (completedResult result)

end RustHammer.Spec
