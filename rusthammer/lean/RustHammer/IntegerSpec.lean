import RustHammer.SignedBitsSpec

open RustHammer.Code.input_types

open Aeneas Aeneas.Std

namespace RustHammer.Spec
open Code

/-- Fixed-width unsigned decoding, specified by positional binary independently
of the narrowing cast. The output type determines the field width. -/
def unsignedIntegerSuccess (ty : UScalarTy) (input : Slice U8) (cursor : Cursor)
    (result : ParseResult (UScalar ty)) : Prop :=
  ∃ next value, result = .Ok (next, value) ∧ validCursor input next ∧
    position next = position cursor + ty.numBits ∧
    value.val = unsignedBits input (position cursor) ty.numBits

def unsignedIntegerOutcome (ty : UScalarTy) (input : Slice U8) (cursor : Cursor)
    (result : ParseResult (UScalar ty)) : Prop :=
  if validCursor input cursor then
    if position cursor + ty.numBits ≤ 8 * input.val.length then
      unsignedIntegerSuccess ty input cursor result
    else result = .Err .UnexpectedEnd
  else result = .Err .InvalidCursor

/-- Fixed-width signed decoding uses mathematical two's-complement interpretation
and returns the corresponding native signed scalar without losing information. -/
def signedIntegerSuccess (ty : IScalarTy) (input : Slice U8) (cursor : Cursor)
    (result : ParseResult (IScalar ty)) : Prop :=
  ∃ next value, result = .Ok (next, value) ∧ validCursor input next ∧
    position next = position cursor + ty.numBits ∧
    value.val = signedValue ty.numBits (unsignedBits input (position cursor) ty.numBits)

def signedIntegerOutcome (ty : IScalarTy) (input : Slice U8) (cursor : Cursor)
    (result : ParseResult (IScalar ty)) : Prop :=
  if validCursor input cursor then
    if position cursor + ty.numBits ≤ 8 * input.val.length then
      signedIntegerSuccess ty input cursor result
    else result = .Err .UnexpectedEnd
  else result = .Err .InvalidCursor

end RustHammer.Spec
