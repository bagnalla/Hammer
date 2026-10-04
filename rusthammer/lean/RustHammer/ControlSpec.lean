import RustHammer.BitsSpec

open Aeneas Aeneas.Std

namespace RustHammer.Spec
open Code

deriving instance DecidableEq for ParseError

/-- A literal contains a validated numeric parser and a representable value. -/
abbrev validLiteral (parser : Literal) : Prop :=
  validBits parser.bits ∧ parser.value.val < 2 ^ parser.bits.width.val

/-- An invalid width takes precedence over an unrepresentable literal value. -/
def literalNewOutcome (width : U8) (value : U64)
    (result : core.result.Result Literal ConfigError) : Prop :=
  if width.val ≤ 64 then
    if value.val < 2 ^ width.val then result = .Ok { bits := { width }, value }
    else result = .Err .InvalidLiteral
  else result = .Err .InvalidWidth

/-- Only input rejection allows another alternative on a complete input buffer. -/
abbrev recoverable (error : ParseError) : Prop :=
  error = .Mismatch ∨ error = .UnexpectedEnd ∨ error = .TrailingInput

/-- Match the decoded numeric value, preserving any earlier parsing error. -/
def literalResult (expected : U64) : ParseResult U64 → ParseResult U64
  | .Err error => .Err error
  | .Ok (next, value) =>
    if value.val = expected.val then .Ok (next, value) else .Err .Mismatch

/-- A validated literal checks the numeric field's cursor and input requirements,
then compares the decoded value. -/
def literalOutcome (input : Slice U8) (cursor : Cursor) (width : U8) (expected : U64)
    (result : ParseResult U64) : Prop :=
  ∃ numeric, bitsOutcome input cursor width numeric ∧ result = literalResult expected numeric

/-- End-of-input preserves the cursor and accepts only the exact end bit position. -/
def endOutcome (input : Slice U8) (cursor : Cursor) (result : ParseResult Unit) : Prop :=
  if validCursor input cursor then
    if position cursor = 8 * input.val.length then result = .Ok (cursor, ())
    else result = .Err .TrailingInput
  else result = .Err .InvalidCursor

/-- The first success or fatal error wins. A recoverable error selects the second
relation at the original cursor; its result, including any error, is preserved. -/
def choice {α : Type} (first second : Cursor → ParseResult α → Prop)
    (cursor : Cursor) (result : ParseResult α) : Prop :=
  ∃ left, first cursor left ∧ match left with
    | .Ok pair => result = .Ok pair
    | .Err error => if recoverable error then second cursor result else result = .Err error

/-- Optional parsing preserves a present value and its consumption. Ordinary input
rejection means absence at the original cursor; fatal errors remain errors. -/
def optional {α : Type} (child : Cursor → ParseResult α → Prop)
    (cursor : Cursor) (result : ParseResult (Option α)) : Prop :=
  (∃ next value, child cursor (.Ok (next, value)) ∧ result = .Ok (next, some value)) ∨
  (∃ error, child cursor (.Err error) ∧ recoverable error ∧ result = .Ok (cursor, none)) ∨
  (∃ error, child cursor (.Err error) ∧ ¬recoverable error ∧ result = .Err error)

/-- Positive lookahead asserts child success and discards its value and consumption.
Every child error is preserved. -/
def and {α : Type} (child : Cursor → ParseResult α → Prop)
    (cursor : Cursor) (result : ParseResult Unit) : Prop :=
  (∃ next value, child cursor (.Ok (next, value)) ∧ result = .Ok (cursor, ())) ∨
  (∃ error, child cursor (.Err error) ∧ result = .Err error)

/-- Negative lookahead asserts ordinary child rejection at the original cursor.
A match becomes mismatch; cursor and alignment errors cannot establish absence. -/
def not {α : Type} (child : Cursor → ParseResult α → Prop)
    (cursor : Cursor) (result : ParseResult Unit) : Prop :=
  (∃ error, child cursor (.Err error) ∧ recoverable error ∧ result = .Ok (cursor, ())) ∨
  (∃ next value, child cursor (.Ok (next, value)) ∧ result = .Err .Mismatch) ∨
  (∃ error, child cursor (.Err error) ∧ ¬recoverable error ∧ result = .Err error)

/-- A marker tries `CA FE`, then `CA`, and requires the exact end of input. -/
def markerParser : Seq (Choice Literal Literal) End :=
  { first := {
      first := { bits := { width := 16#u8 }, value := 51966#u64 },
      second := { bits := { width := 8#u8 }, value := 202#u64 } },
    second := () }

/-- The marker constructor fixes the grammar as well as validating its literals. -/
abbrev validMarker (parser : Marker) : Prop := parser.parser = markerParser

/-- A marker tries `CA FE`, then `CA`, and requires the exact end of input. -/
def markerOutcome (input : Slice U8) (cursor : Cursor) (result : ParseResult U64) : Prop :=
  ∃ fields, sequence
    (choice (fun start => literalOutcome input start 16#u8 51966#u64)
      (fun start => literalOutcome input start 8#u8 202#u64))
    (endOutcome input) cursor fields ∧
    match fields with
    | .Err error => result = .Err error
    | .Ok (next, (value, ())) => result = .Ok (next, value)

end RustHammer.Spec
