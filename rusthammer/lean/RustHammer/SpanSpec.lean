import RustHammer.PositionSpec

open RustHammer.Code.input_types
  RustHammer.Code.span_types

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
def checked (input : Slice U8) (start finish : Cursor) :
    core.result.Result BitSpan ParseError :=
  if validCursor input.val.length start ∧ validCursor input.val.length finish then
    if Spec.position start ≤ Spec.position finish then .Ok ⟨input, start, finish⟩
    else .Err .NonProgress
  else .Err .InvalidCursor

def attach {α : Type} (input : Slice U8) (start : Cursor)
    (child : Spec.ParseResult α) : Spec.ParseResult (α × BitSpan) :=
  match child with
  | .Ok (finish, value) => match checked input start finish with
    | .Ok span => .Ok (finish, (value, span))
    | .Err error => .Err error
  | .Err error => .Err error
def discard {α : Type} (outcome : Spec.ParseResult (α × BitSpan)) : Spec.ParseResult BitSpan :=
  match outcome with
  | .Ok (finish, (_, span)) => .Ok (finish, span)
  | .Err error => .Err error
/-- The child runs only for a valid entry. A successful endpoint is checked
before a span is returned. -/
def capture {α : Type} (input : Slice U8) (start : Cursor)
    (child : Spec.ParseResult α → Prop) (result : Spec.ParseResult (α × BitSpan)) : Prop :=
  if validCursor input.val.length start then
    ∃ outcome, child outcome ∧ result = attach input start outcome
  else result = .Err .InvalidCursor

def recognize {α : Type} (input : Slice U8) (start : Cursor)
    (child : Spec.ParseResult α → Prop) (result : Spec.ParseResult BitSpan) : Prop :=
  ∃ captured, capture input start child captured ∧ result = discard captured

/-- Complete source bytes are available exactly when both endpoints are aligned. -/
def byteView (span : BitSpan) (result : Option (Slice U8)) : Prop :=
  if span.start.bit.val = 0 ∧ span.end.bit.val = 0 then
    ∃ bytes, result = some bytes ∧
      bytes.val = (span.input.val.drop span.start.byte.val).take (span.end.byte.val - span.start.byte.val)
  else result = none

end

/-- Convert a physical bit (numbered from the low end) into a consumed-bit offset.
This identifies the set of selected bits, not their internal decoding order. -/
def offset (byte bit : Nat) : Nat :=
  8 * byte + (7 - bit)

def selected (span : BitSpan) (byte bit : Nat) : Prop :=
  bit < 8 ∧ Spec.position span.start ≤ offset byte bit ∧
    offset byte bit < Spec.position span.end

def physical (index : Nat) : Nat × Nat :=
  (index / 8, 7 - index % 8)

/-- Mathematical enumeration only; no runtime allocation or iterator is implied. -/
def bits (span : BitSpan) : List (Nat × Nat) :=
  (List.range' (Spec.position span.start) (Spec.position span.end - Spec.position span.start)).map
    physical

end RustHammer.Span
