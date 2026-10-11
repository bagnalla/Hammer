import RustHammer.OrderMath
import RustHammer.IntegerSpec
import RustHammer.ByteSpec

open RustHammer.Code.input_types

open Aeneas Aeneas.Std

namespace RustHammer.Ordering
open Code

def literalOutcome (input : Slice U8) (cursor : Cursor) (width : U8) (expected : U64)
    (order : ByteOrder) (result : Spec.ParseResult U64) : Prop :=
  ∃ numeric, outcome input cursor width order numeric ∧ result = Spec.literalResult expected numeric

def signedBitsSuccess (input : Slice U8) (cursor : Cursor) (width : U8) (order : ByteOrder)
    (result : Spec.ParseResult I64) : Prop :=
  ∃ next value, result = .Ok (next, value) ∧ Spec.validCursor input next ∧
    Spec.position next = Spec.position cursor + width.val ∧
    value.val = Spec.signedValue width.val (unsigned input order (Spec.position cursor) width.val)

def signedBitsOutcome (input : Slice U8) (cursor : Cursor) (width : U8) (order : ByteOrder)
    (result : Spec.ParseResult I64) : Prop :=
  if Spec.validCursor input cursor then
    if Spec.position cursor + width.val ≤ 8 * input.val.length then
      signedBitsSuccess input cursor width order result
    else result = .Err .UnexpectedEnd
  else result = .Err .InvalidCursor

def unsignedIntegerSuccess (ty : UScalarTy) (input : Slice U8) (cursor : Cursor) (order : ByteOrder)
    (result : Spec.ParseResult (UScalar ty)) : Prop :=
  ∃ next value, result = .Ok (next, value) ∧ Spec.validCursor input next ∧
    Spec.position next = Spec.position cursor + ty.numBits ∧
    value.val = unsigned input order (Spec.position cursor) ty.numBits

def unsignedIntegerOutcome (ty : UScalarTy) (input : Slice U8) (cursor : Cursor) (order : ByteOrder)
    (result : Spec.ParseResult (UScalar ty)) : Prop :=
  if Spec.validCursor input cursor then
    if Spec.position cursor + ty.numBits ≤ 8 * input.val.length then
      unsignedIntegerSuccess ty input cursor order result
    else result = .Err .UnexpectedEnd
  else result = .Err .InvalidCursor

def signedIntegerSuccess (ty : IScalarTy) (input : Slice U8) (cursor : Cursor) (order : ByteOrder)
    (result : Spec.ParseResult (IScalar ty)) : Prop :=
  ∃ next value, result = .Ok (next, value) ∧ Spec.validCursor input next ∧
    Spec.position next = Spec.position cursor + ty.numBits ∧
    value.val = Spec.signedValue ty.numBits (unsigned input order (Spec.position cursor) ty.numBits)

def signedIntegerOutcome (ty : IScalarTy) (input : Slice U8) (cursor : Cursor) (order : ByteOrder)
    (result : Spec.ParseResult (IScalar ty)) : Prop :=
  if Spec.validCursor input cursor then
    if Spec.position cursor + ty.numBits ≤ 8 * input.val.length then
      signedIntegerSuccess ty input cursor order result
    else result = .Err .UnexpectedEnd
  else result = .Err .InvalidCursor

def matchBytes (input : Slice U8) (context : ByteOrder) :
    List U8 → Cursor → Spec.ParseResult Unit → Prop
  | [], cursor, result => result = .Ok (cursor, ())
  | expected :: rest, cursor, result =>
    ∃ decoded, (unsignedIntegerOutcome .U8 input cursor context) decoded ∧
      match decoded with
      | .Ok (next, value) => if value = expected then matchBytes input context rest next result
          else result = .Err .Mismatch
      | .Err error => result = .Err error
def bytePatternOutcome (input : Slice U8) (context : ByteOrder) (pattern : Slice U8)
    (cursor : Cursor) (result : Spec.ParseResult (Slice U8)) : Prop :=
  match result with
  | .Ok (next, output) => output = pattern ∧ matchBytes input context pattern.val cursor (.Ok (next, ()))
  | .Err error => matchBytes input context pattern.val cursor (.Err error)
@[simp] theorem byte_outcome_default (input : Slice U8) (cursor : Cursor)
    (result : Spec.ParseResult U8) :
    unsignedIntegerOutcome .U8 input cursor .Big result ↔ Spec.byteOutcome input cursor result := by
  simp only [unsignedIntegerOutcome, unsignedIntegerSuccess, Spec.byteOutcome,
    Spec.byteSuccess, unsigned_default, UScalarTy.U8_numBits_eq]

@[simp] theorem match_bytes_default (input : Slice U8) (pattern : List U8) (cursor : Cursor)
    (result : Spec.ParseResult Unit) :
    matchBytes input .Big pattern cursor result ↔ Spec.matchBytes input pattern cursor result := by
  induction pattern generalizing cursor result with
  | nil => rfl
  | cons expected rest ih =>
    simp only [matchBytes, Spec.matchBytes, byte_outcome_default]
    apply exists_congr
    intro decoded
    cases decoded with
    | Err error => rfl
    | Ok pair =>
      rcases pair with ⟨next, value⟩
      simp only [ih]

@[simp] theorem byte_pattern_default (input : Slice U8) (pattern : Slice U8) (cursor : Cursor)
    (result : Spec.ParseResult (Slice U8)) :
    bytePatternOutcome input .Big pattern cursor result ↔
      Spec.bytePatternOutcome input pattern cursor result := by
  cases result <;> simp only [bytePatternOutcome, Spec.bytePatternOutcome, match_bytes_default]

end RustHammer.Ordering
