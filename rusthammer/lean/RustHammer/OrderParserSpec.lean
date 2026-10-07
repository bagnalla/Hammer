import RustHammer.OrderMath
import RustHammer.IntegerSpec
import RustHammer.ByteSpec

open RustHammer.Code.input_types

open Aeneas Aeneas.Std

namespace RustHammer.Ordering
open Code

def literalOutcome (input : Slice U8) (cursor : Cursor) (width : U8) (expected : U64)
    (order : Order) (result : Spec.ParseResult U64) : Prop :=
  ∃ numeric, outcome input cursor width order numeric ∧ result = Spec.literalResult expected numeric

def signedBitsSuccess (input : Slice U8) (cursor : Cursor) (width : U8) (order : Order)
    (result : Spec.ParseResult I64) : Prop :=
  ∃ next value, result = .Ok (next, value) ∧ Spec.validCursor input next ∧
    Spec.position next = Spec.position cursor + width.val ∧
    value.val = Spec.signedValue width.val (unsigned input order (Spec.position cursor) width.val)

def signedBitsOutcome (input : Slice U8) (cursor : Cursor) (width : U8) (order : Order)
    (result : Spec.ParseResult I64) : Prop :=
  if Spec.validCursor input cursor then
    if Spec.position cursor + width.val ≤ 8 * input.val.length then
      signedBitsSuccess input cursor width order result
    else result = .Err .UnexpectedEnd
  else result = .Err .InvalidCursor

def unsignedIntegerSuccess (ty : UScalarTy) (input : Slice U8) (cursor : Cursor) (order : Order)
    (result : Spec.ParseResult (UScalar ty)) : Prop :=
  ∃ next value, result = .Ok (next, value) ∧ Spec.validCursor input next ∧
    Spec.position next = Spec.position cursor + ty.numBits ∧
    value.val = unsigned input order (Spec.position cursor) ty.numBits

def unsignedIntegerOutcome (ty : UScalarTy) (input : Slice U8) (cursor : Cursor) (order : Order)
    (result : Spec.ParseResult (UScalar ty)) : Prop :=
  if Spec.validCursor input cursor then
    if Spec.position cursor + ty.numBits ≤ 8 * input.val.length then
      unsignedIntegerSuccess ty input cursor order result
    else result = .Err .UnexpectedEnd
  else result = .Err .InvalidCursor

def signedIntegerSuccess (ty : IScalarTy) (input : Slice U8) (cursor : Cursor) (order : Order)
    (result : Spec.ParseResult (IScalar ty)) : Prop :=
  ∃ next value, result = .Ok (next, value) ∧ Spec.validCursor input next ∧
    Spec.position next = Spec.position cursor + ty.numBits ∧
    value.val = Spec.signedValue ty.numBits (unsigned input order (Spec.position cursor) ty.numBits)

def signedIntegerOutcome (ty : IScalarTy) (input : Slice U8) (cursor : Cursor) (order : Order)
    (result : Spec.ParseResult (IScalar ty)) : Prop :=
  if Spec.validCursor input cursor then
    if Spec.position cursor + ty.numBits ≤ 8 * input.val.length then
      signedIntegerSuccess ty input cursor order result
    else result = .Err .UnexpectedEnd
  else result = .Err .InvalidCursor

def matchBytes (input : Slice U8) (context : ParseContext) :
    List U8 → Cursor → ParseOutcome Unit → Prop
  | [], cursor, result => result = .Success cursor ()
  | expected :: rest, cursor, result =>
    ∃ decoded, Partial.primitive context.status
      (unsignedIntegerOutcome .U8 input cursor context.order) decoded ∧
      match decoded with
      | .Success next value => if value = expected then matchBytes input context rest next result
          else result = .Error .Mismatch
      | .Error error => result = .Error error
      | .NeedMore => result = .NeedMore

def bytePatternOutcome (input : Slice U8) (context : ParseContext) (pattern : Slice U8)
    (cursor : Cursor) (result : ParseOutcome (Slice U8)) : Prop :=
  match result with
  | .Success next output => output = pattern ∧ matchBytes input context pattern.val cursor (.Success next ())
  | .Error error => matchBytes input context pattern.val cursor (.Error error)
  | .NeedMore => matchBytes input context pattern.val cursor .NeedMore

end RustHammer.Ordering
