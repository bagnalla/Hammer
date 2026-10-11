import RustHammer.ControlSpec

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
a truncated byte reports UnexpectedEnd. The empty list is the identity,
including for raw cursors. This definition uses no machine counter or indexing. -/
def matchBytes (input : Slice U8) :
    List U8 → Cursor → Spec.ParseResult Unit → Prop
  | [], cursor, outcome => outcome = .Ok (cursor, ())
  | expected :: rest, cursor, outcome =>
    ∃ decoded, (byteOutcome input cursor) decoded ∧
      match decoded with
      | .Ok (next, value) => if value = expected then matchBytes input rest next outcome
          else outcome = .Err .Mismatch
      | .Err error => outcome = .Err error
/-- Successful output is the configured pattern, independently of the input's
storage. Slice identity is checked by Rust tests; the Lean slice model is by value. -/
def bytePatternOutcome (input : Slice U8) (pattern : Slice U8)
    (cursor : Cursor) (outcome : Spec.ParseResult (Slice U8)) : Prop :=
  match outcome with
  | .Ok (next, output) => output = pattern ∧ matchBytes input pattern.val cursor (.Ok (next, ()))
  | .Err error => matchBytes input pattern.val cursor (.Err error)
end RustHammer.Spec
