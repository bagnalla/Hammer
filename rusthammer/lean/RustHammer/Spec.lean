import RustHammer.Rusthammer

open Aeneas Aeneas.Std

namespace RustHammer.Spec
open Code

abbrev ParseResult (α : Type) := core.result.Result (Cursor × α) ParseError

/-- Embed a complete parsing result in the three-outcome interface. -/
def completedResult {α : Type} : ParseResult α → ParseOutcome α
  | .Ok (next, value) => .Success next value
  | .Err error => .Error error

/-- A final-input contract preserves the earlier complete-buffer specification
and rules out NeedMore, rather than merely converting it into an error. -/
def completed {α : Type} (contract : ParseResult α → Prop) (outcome : ParseOutcome α) : Prop :=
  ∃ result, contract result ∧ outcome = completedResult result

@[simp] theorem completed_success {α : Type} (contract : ParseResult α → Prop)
    (cursor : Cursor) (value : α) :
    completed contract (.Success cursor value) ↔ contract (.Ok (cursor, value)) := by
  constructor
  · rintro ⟨result, h, heq⟩
    cases result with
    | Err _ => cases heq
    | Ok pair => cases pair; cases heq; exact h
  · intro h
    exact ⟨.Ok (cursor, value), h, rfl⟩

@[simp] theorem completed_error {α : Type} (contract : ParseResult α → Prop)
    (error : ParseError) : completed contract (.Error error) ↔ contract (.Err error) := by
  constructor
  · rintro ⟨result, h, heq⟩
    cases result with
    | Err _ => cases heq; exact h
    | Ok pair => cases pair; cases heq
  · intro h
    exact ⟨.Err error, h, rfl⟩

@[simp] theorem completed_embed {α : Type} (contract : ParseResult α → Prop)
    (result : ParseResult α) : completed contract (completedResult result) ↔ contract result := by
  cases result with
  | Err _ => exact completed_error _ _
  | Ok pair => cases pair; exact completed_success _ _ _

/-- Logical bit position uses unbounded naturals, independently of machine arithmetic. -/
def position (cursor : Cursor) : Nat := 8 * cursor.byte.val + cursor.bit.val

/-- A successful MSB-first read selects the corresponding bit in the current byte. -/
def bitSuccess (input : Slice U8) (cursor : Cursor) (result : ParseResult Bool) : Prop :=
  ∃ next value, result = .Ok (next, value) ∧
    next.byte.val = cursor.byte.val + (if cursor.bit.val = 7 then 1 else 0) ∧
    next.bit.val = (cursor.bit.val + 1) % 8 ∧
    value = (input.val[cursor.byte.val]!).val.testBit (7 - cursor.bit.val)

/-- Complete one-bit semantics, including invalid cursors and exhausted input. -/
def bitOutcome (input : Slice U8) (cursor : Cursor) (result : ParseResult Bool) : Prop :=
  if cursor.bit.val < 8 ∧ cursor.byte.val < input.val.length then
    bitSuccess input cursor result
  else result = .Err
    (if cursor.bit.val < 8 ∧ cursor.byte.val = input.val.length ∧ cursor.bit.val = 0
     then ParseError.UnexpectedEnd else ParseError.InvalidCursor)

/-- Relational sequencing, including either child's ordinary parsing error. -/
def sequence {α β : Type}
    (first : Cursor → ParseResult α → Prop)
    (second : Cursor → ParseResult β → Prop)
    (cursor : Cursor) (result : ParseResult (α × β)) : Prop :=
  ∃ left, first cursor left ∧ match left with
    | .Err error => result = .Err error
    | .Ok (middle, a) => ∃ right, second middle right ∧ match right with
      | .Err error => result = .Err error
      | .Ok (last, b) => result = .Ok (last, (a, b))

/-- Mapping changes only a successful value, preserving consumption and child errors. -/
def map {α β : Type} (child : Cursor → ParseResult α → Prop)
    (mapping : α → β → Prop) (cursor : Cursor) (result : ParseResult β) : Prop :=
  ∃ parsed, child cursor parsed ∧ match parsed with
    | .Err error => result = .Err error
    | .Ok (next, value) => ∃ mapped, mapping value mapped ∧ result = .Ok (next, mapped)

/-- Verification preserves accepted outputs and turns predicate rejection into mismatch. -/
def verify {α : Type} (child : Cursor → ParseResult α → Prop)
    (predicate : α → Prop) [DecidablePred predicate]
    (cursor : Cursor) (result : ParseResult α) : Prop :=
  ∃ parsed, child cursor parsed ∧ match parsed with
    | .Err error => result = .Err error
    | .Ok (next, value) =>
      if predicate value then result = .Ok (next, value) else result = .Err .Mismatch

/-- The example grammar is exactly three consecutive bits, in field order. -/
def flagsOutcome (input : Slice U8) (cursor : Cursor) (result : ParseResult Flags) : Prop :=
  ∃ fields, sequence (bitOutcome input)
    (sequence (bitOutcome input) (bitOutcome input)) cursor fields ∧
    match fields with
    | .Err error => result = .Err error
    | .Ok (next, (urgent, (encrypted, compressed))) =>
      result = .Ok (next, { urgent, encrypted, compressed })

/-- An aligned payload is the requested subsequence, with exact byte consumption. -/
def takeAlignedSuccess (input : Slice U8) (cursor : Cursor) (count : Usize)
    (result : ParseResult (Slice U8)) : Prop :=
  ∃ next payload, result = .Ok (next, payload) ∧
    next.byte.val = cursor.byte.val + count.val ∧ next.bit = 0#u8 ∧
    payload.val = (input.val.drop cursor.byte.val).take count.val

/-- Cursor validity takes precedence over alignment, then bounds. At canonical
end-of-input, an empty payload succeeds and a nonempty one is truncated. Bounds
use natural arithmetic, even when the requested end exceeds machine limits. -/
def takeAlignedOutcome (input : Slice U8) (cursor : Cursor) (count : Usize)
    (result : ParseResult (Slice U8)) : Prop :=
  if cursor.bit.val < 8 ∧ cursor.byte.val ≤ input.val.length ∧
      (cursor.byte.val = input.val.length → cursor.bit.val = 0) then
    if cursor.bit.val = 0 then
      if cursor.byte.val + count.val ≤ input.val.length then
        takeAlignedSuccess input cursor count result
      else result = .Err ParseError.UnexpectedEnd
    else result = .Err ParseError.Unaligned
  else result = .Err ParseError.InvalidCursor

end RustHammer.Spec
