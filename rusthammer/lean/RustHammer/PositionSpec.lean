import RustHammer.PartialSpec

open RustHammer.Code.input_types

open Aeneas Aeneas.Std

namespace RustHammer.Spec
open Code

/-- Validity for an arbitrary mathematical input length, independent of storage. -/
abbrev validPosition (length : Nat) (cursor : Cursor) : Prop :=
  cursor.bit.val < 8 ∧ position cursor ≤ 8 * length

/-- Advancing is specified by unbounded addition and input bounds, without
requiring the absolute bit position or the requested end to fit in usize. -/
def advanceOutcome (length : Nat) (cursor : Cursor) (bits : Nat)
    (result : core.result.Result Cursor ParseError) : Prop :=
  if validPosition length cursor then
    if position cursor + bits ≤ 8 * length then
      ∃ next, result = .Ok next ∧ validPosition length next ∧
        position next = position cursor + bits
    else result = .Err .UnexpectedEnd
  else result = .Err .InvalidCursor

def skipBitsOutcome (input : Slice U8) (cursor : Cursor) (bits : Usize)
    (result : ParseResult Unit) : Prop :=
  ∃ advanced, advanceOutcome input.val.length cursor bits.val advanced ∧
    result = match advanced with
      | .Ok next => .Ok (next, ())
      | .Err error => .Err error

/-- Tell reports and preserves the supplied cursor after validating it.
Input finality has no bearing on its result. -/
def tellOutcome (input : Slice U8) (cursor : Cursor) (result : ParseResult Cursor) : Prop :=
  if validCursor input cursor then result = .Ok (cursor, cursor)
  else result = .Err .InvalidCursor

end RustHammer.Spec
