import RustHammer.PositionSpec

open Aeneas Aeneas.Std

namespace RustHammer.Span
open Code

def validCursor (length : Nat) (cursor : Cursor) : Prop :=
  Spec.validPosition length cursor

/-- Endpoint validity and forward consumption use mathematical bit positions. -/
def valid (span : BitSpan) : Prop :=
  validCursor span.input.val.length span.start ∧
  validCursor span.input.val.length span.end ∧
  Spec.position span.start ≤ Spec.position span.end

noncomputable section
open Classical

/-- Invalid endpoints take precedence over backward consumption. -/
def checked (input : Slice U8) (start finish : Cursor) (order : BitOrder) :
    core.result.Result BitSpan ParseError :=
  if validCursor input.val.length start ∧ validCursor input.val.length finish then
    if Spec.position start ≤ Spec.position finish then .Ok ⟨input, start, finish, order⟩
    else .Err .NonProgress
  else .Err .InvalidCursor

def attach {α : Type} (input : Slice U8) (start : Cursor) (order : BitOrder)
    (child : ParseOutcome α) : ParseOutcome (α × BitSpan) :=
  match child with
  | .Success finish value => match checked input start finish order with
    | .Ok span => .Success finish (value, span)
    | .Err error => .Error error
  | .Error error => .Error error
  | .NeedMore => .NeedMore

def discard {α : Type} (outcome : ParseOutcome (α × BitSpan)) : ParseOutcome BitSpan :=
  match outcome with
  | .Success finish (_, span) => .Success finish span
  | .Error error => .Error error
  | .NeedMore => .NeedMore

/-- The child runs only for a valid entry. Its state is retained even if span
validation subsequently rejects its successful endpoint. -/
def capture {State α : Type} (input : Slice U8) (start : Cursor) (order : BitOrder)
    (state : State) (child : ParseOutcome α × State → Prop)
    (result : ParseOutcome (α × BitSpan) × State) : Prop :=
  if validCursor input.val.length start then
    ∃ outcome final, child (outcome, final) ∧ result = (attach input start order outcome, final)
  else result = (.Error .InvalidCursor, state)

def recognize {State α : Type} (input : Slice U8) (start : Cursor) (order : BitOrder)
    (state : State) (child : ParseOutcome α × State → Prop)
    (result : ParseOutcome BitSpan × State) : Prop :=
  ∃ captured final, capture input start order state child (captured, final) ∧
    result = (discard captured, final)

/-- Complete source bytes are available exactly when both endpoints are aligned. -/
def byteView (span : BitSpan) (result : Option (Slice U8)) : Prop :=
  if span.start.bit.val = 0 ∧ span.end.bit.val = 0 then
    ∃ bytes, result = some bytes ∧
      bytes.val = (span.input.val.drop span.start.byte.val).take (span.end.byte.val - span.start.byte.val)
  else result = none

end

/-- Convert a physical bit (numbered from the low end) into a consumed-bit offset.
This identifies the set of selected bits, not their internal decoding order. -/
def offset (order : BitOrder) (byte bit : Nat) : Nat :=
  8 * byte + match order with | .HighFirst => 7 - bit | .LowFirst => bit

def selected (span : BitSpan) (byte bit : Nat) : Prop :=
  bit < 8 ∧ Spec.position span.start ≤ offset span.bit_order byte bit ∧
    offset span.bit_order byte bit < Spec.position span.end

def physical (order : BitOrder) (index : Nat) : Nat × Nat :=
  (index / 8, match order with | .HighFirst => 7 - index % 8 | .LowFirst => index % 8)

/-- Mathematical enumeration only; no runtime allocation or iterator is implied. -/
def bits (span : BitSpan) : List (Nat × Nat) :=
  (List.range' (Spec.position span.start) (Spec.position span.end - Spec.position span.start)).map
    (physical span.bit_order)

end RustHammer.Span
