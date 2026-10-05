import RustHammer.IntegerSpec
import RustHammer.SignedBitsProofs
import RustHammer.ByteProofs

open Aeneas Aeneas.Std Result WP

namespace RustHammer.Proofs
open Code

private theorem primitive_ok {α : Type} (status : InputStatus) (next : Cursor) (value : α) :
    Partial.primitiveResult status (.Ok (next, value)) = .Success next value := by
  cases status <;> rfl

/-- Shared proof for the unsigned readers' lossless casts and outcome propagation. -/
private theorem narrow_unsigned_spec (ty : UScalarTy) (width : U8)
    (input : Slice U8) (cursor : Cursor) (status : InputStatus)
    (hwidth : width.val = ty.numBits) (hconfig : width.val ≤ 64) :
    (do
      let parsed ← Bits.Insts.RusthammerParserInputU64.parse_with { width } input cursor (Spec.defaultContext status)
      match parsed with
      | .Success next value =>
        let narrowed ← lift (UScalar.cast ty value)
        ok (ParseOutcome.Success next narrowed)
      | .Error error => ok (.Error error)
      | .NeedMore => ok .NeedMore)
      ⦃ result => Partial.primitive status (Spec.unsignedIntegerOutcome ty input cursor) result ⦄ := by
  step with bits_with_spec { width } input cursor status hconfig as ⟨outcome, houtcome⟩
  rcases houtcome with ⟨parsed, hparsed, rfl⟩
  by_cases hvalid : Spec.validCursor input cursor
  · by_cases hfit : Spec.position cursor + width.val ≤ 8 * input.val.length
    · simp only [Spec.bitsOutcome, if_pos hvalid, if_pos hfit] at hparsed
      rcases hparsed with ⟨next, value, rfl, hnext, hpos, hvalue⟩
      rw [primitive_ok]
      have hbound := unsignedBits_lt_pow input (Spec.position cursor) width.val
      have hinBounds : value.val ≤ UScalar.max ty := by
        rw [UScalar.max, ← hwidth]
        omega
      step with UScalar.cast_inBounds_spec ty value hinBounds as ⟨narrowed, hnarrowed⟩
      refine ⟨.Ok (next, narrowed), ?_, (primitive_ok status next narrowed).symm⟩
      simp only [Spec.unsignedIntegerOutcome, if_pos hvalid, ← hwidth, if_pos hfit,
        Spec.unsignedIntegerSuccess]
      exact ⟨next, narrowed, rfl, hnext, by simpa [hwidth] using hpos,
        by simpa [hnarrowed, hwidth] using hvalue⟩
    · have heq : parsed = .Err .UnexpectedEnd := by
        simpa only [Spec.bitsOutcome, if_pos hvalid, if_neg hfit] using hparsed
      subst parsed
      cases status <;> simp only [Partial.primitiveResult, Spec.completedResult, spec_ok]
      all_goals exact ⟨.Err .UnexpectedEnd,
        by simp only [Spec.unsignedIntegerOutcome, if_pos hvalid, ← hwidth, if_neg hfit], rfl⟩
  · have heq : parsed = .Err .InvalidCursor := by
      simpa only [Spec.bitsOutcome, if_neg hvalid] using hparsed
    subst parsed
    cases status <;> simp only [Partial.primitiveResult, Spec.completedResult, spec_ok]
    all_goals exact ⟨.Err .InvalidCursor,
      by simp only [Spec.unsignedIntegerOutcome, if_neg hvalid], rfl⟩

/-- Signed field bounds justify native signed narrowing, including each minimum. -/
private theorem narrow_signed_spec (ty : IScalarTy) (width : U8)
    (input : Slice U8) (cursor : Cursor) (status : InputStatus)
    (hwidth : width.val = ty.numBits) (hconfig : width.val ≤ 64) :
    (do
      let parsed ← SignedBits.Insts.RusthammerParserInputI64.parse_with
        { bits := { width } } input cursor (Spec.defaultContext status)
      match parsed with
      | .Success next value =>
        let narrowed ← lift (IScalar.cast ty value)
        ok (ParseOutcome.Success next narrowed)
      | .Error error => ok (.Error error)
      | .NeedMore => ok .NeedMore)
      ⦃ result => Partial.primitive status (Spec.signedIntegerOutcome ty input cursor) result ⦄ := by
  step with signed_bits_with_spec { bits := { width } } input cursor status hconfig
    as ⟨outcome, houtcome⟩
  rcases houtcome with ⟨parsed, hparsed, rfl⟩
  by_cases hvalid : Spec.validCursor input cursor
  · by_cases hfit : Spec.position cursor + width.val ≤ 8 * input.val.length
    · simp only [Spec.signedBitsOutcome, if_pos hvalid, if_pos hfit] at hparsed
      rcases hparsed with ⟨next, value, rfl, hnext, hpos, hvalue⟩
      rw [primitive_ok]
      have hbound := signed_value_bounds width.val
        (Spec.unsignedBits input (Spec.position cursor) width.val)
        (by rw [hwidth]; exact Nat.pos_of_ne_zero (IScalarTy.numBits_nonzero ty))
        (unsignedBits_lt_pow input (Spec.position cursor) width.val)
      have hinBounds : IScalar.min ty ≤ value.val ∧ value.val ≤ IScalar.max ty := by
        simp only [Nat.cast_pow, Nat.cast_ofNat] at hbound
        simp only [IScalar.min, IScalar.max, ← hwidth]
        omega
      step with IScalar.cast_inBounds_spec ty value hinBounds as ⟨narrowed, hnarrowed⟩
      refine ⟨.Ok (next, narrowed), ?_, (primitive_ok status next narrowed).symm⟩
      simp only [Spec.signedIntegerOutcome, if_pos hvalid, ← hwidth, if_pos hfit,
        Spec.signedIntegerSuccess]
      exact ⟨next, narrowed, rfl, hnext, by simpa [hwidth] using hpos,
        by simpa [hnarrowed, hwidth] using hvalue⟩
    · have heq : parsed = .Err .UnexpectedEnd := by
        simpa only [Spec.signedBitsOutcome, if_pos hvalid, if_neg hfit] using hparsed
      subst parsed
      cases status <;> simp only [Partial.primitiveResult, Spec.completedResult, spec_ok]
      all_goals exact ⟨.Err .UnexpectedEnd,
        by simp only [Spec.signedIntegerOutcome, if_pos hvalid, ← hwidth, if_neg hfit], rfl⟩
  · have heq : parsed = .Err .InvalidCursor := by
      simpa only [Spec.signedBitsOutcome, if_neg hvalid] using hparsed
    subst parsed
    cases status <;> simp only [Partial.primitiveResult, Spec.completedResult, spec_ok]
    all_goals exact ⟨.Err .InvalidCursor,
      by simp only [Spec.signedIntegerOutcome, if_neg hvalid], rfl⟩

theorem be_u16_with_spec (input : Slice U8) (cursor : Cursor) (status : InputStatus) :
    BeU16.Insts.RusthammerParserInputU16.parse_with () input cursor (Spec.defaultContext status)
      ⦃ result => Partial.primitive status (Spec.unsignedIntegerOutcome .U16 input cursor) result ⦄ := by
  unfold BeU16.Insts.RusthammerParserInputU16.parse_with
  simp only [Spec.default_order_pin]
  exact narrow_unsigned_spec .U16 16#u8 input cursor status rfl (by decide)

theorem be_u32_with_spec (input : Slice U8) (cursor : Cursor) (status : InputStatus) :
    BeU32.Insts.RusthammerParserInputU32.parse_with () input cursor (Spec.defaultContext status)
      ⦃ result => Partial.primitive status (Spec.unsignedIntegerOutcome .U32 input cursor) result ⦄ := by
  unfold BeU32.Insts.RusthammerParserInputU32.parse_with
  simp only [Spec.default_order_pin]
  exact narrow_unsigned_spec .U32 32#u8 input cursor status rfl (by decide)

theorem be_u64_with_spec (input : Slice U8) (cursor : Cursor) (status : InputStatus) :
    BeU64.Insts.RusthammerParserInputU64.parse_with () input cursor (Spec.defaultContext status)
      ⦃ result => Partial.primitive status (Spec.unsignedIntegerOutcome .U64 input cursor) result ⦄ := by
  unfold BeU64.Insts.RusthammerParserInputU64.parse_with
  simp only [Spec.default_order_pin]
  step with bits_with_spec { width := 64#u8 } input cursor status (by decide) as ⟨outcome, houtcome⟩
  have h : Partial.primitive status (Spec.unsignedIntegerOutcome .U64 input cursor) outcome := by
    simpa only [Partial.primitive, Spec.bitsOutcome, Spec.bitsSuccess, Spec.unsignedIntegerOutcome,
      Spec.unsignedIntegerSuccess, UScalar.ofNatCore_val_eq, UScalarTy.U64_numBits_eq] using houtcome
  cases outcome <;> simpa only [spec_ok] using h

theorem i8_with_spec (input : Slice U8) (cursor : Cursor) (status : InputStatus) :
    Code.I8.Insts.RusthammerParserInputI8.parse_with () input cursor (Spec.defaultContext status)
      ⦃ result => Partial.primitive status (Spec.signedIntegerOutcome .I8 input cursor) result ⦄ := by
  exact narrow_signed_spec .I8 8#u8 input cursor status rfl (by decide)

theorem be_i16_with_spec (input : Slice U8) (cursor : Cursor) (status : InputStatus) :
    BeI16.Insts.RusthammerParserInputI16.parse_with () input cursor (Spec.defaultContext status)
      ⦃ result => Partial.primitive status (Spec.signedIntegerOutcome .I16 input cursor) result ⦄ := by
  unfold BeI16.Insts.RusthammerParserInputI16.parse_with
  simp only [Spec.default_order_pin]
  exact narrow_signed_spec .I16 16#u8 input cursor status rfl (by decide)

theorem be_i32_with_spec (input : Slice U8) (cursor : Cursor) (status : InputStatus) :
    BeI32.Insts.RusthammerParserInputI32.parse_with () input cursor (Spec.defaultContext status)
      ⦃ result => Partial.primitive status (Spec.signedIntegerOutcome .I32 input cursor) result ⦄ := by
  unfold BeI32.Insts.RusthammerParserInputI32.parse_with
  simp only [Spec.default_order_pin]
  exact narrow_signed_spec .I32 32#u8 input cursor status rfl (by decide)

theorem be_i64_with_spec (input : Slice U8) (cursor : Cursor) (status : InputStatus) :
    BeI64.Insts.RusthammerParserInputI64.parse_with () input cursor (Spec.defaultContext status)
      ⦃ result => Partial.primitive status (Spec.signedIntegerOutcome .I64 input cursor) result ⦄ := by
  unfold BeI64.Insts.RusthammerParserInputI64.parse_with
  simp only [Spec.default_order_pin]
  step with signed_bits_with_spec { bits := { width := 64#u8 } } input cursor status (by decide)
    as ⟨outcome, houtcome⟩
  have h : Partial.primitive status (Spec.signedIntegerOutcome .I64 input cursor) outcome := by
    simpa only [Partial.primitive, Spec.signedBitsOutcome, Spec.signedBitsSuccess, Spec.signedIntegerOutcome,
      Spec.signedIntegerSuccess, UScalar.ofNatCore_val_eq, IScalarTy.I64_numBits_eq] using houtcome
  cases outcome <;> simpa only [spec_ok] using h

/-- The existing byte reader is the unsigned eight-bit member of this family. -/
theorem byte_integer_with_spec (input : Slice U8) (cursor : Cursor) (status : InputStatus) :
    Byte.Insts.RusthammerParserInputU8.parse_with () input cursor (Spec.defaultContext status)
      ⦃ result => Partial.primitive status (Spec.unsignedIntegerOutcome .U8 input cursor) result ⦄ := by
  simpa only [Partial.primitive, Spec.byteOutcome, Spec.byteSuccess, Spec.unsignedIntegerOutcome,
    Spec.unsignedIntegerSuccess, UScalarTy.U8_numBits_eq] using byte_with_spec input cursor status

theorem be_u16_final_spec (input : Slice U8) (cursor : Cursor) :
    BeU16.Insts.RusthammerParserInputU16.parse_with () input cursor ParseContext.FINAL
      ⦃ result => Spec.completed (Spec.unsignedIntegerOutcome .U16 input cursor) result ⦄ := by
  simpa only [ParseContext.FINAL, Partial.primitive, Partial.primitiveResult, Spec.completed] using
    be_u16_with_spec input cursor .Final

theorem be_u16_spec (input : Slice U8) (cursor : Cursor) :
    Parser.parse.default BeU16.Insts.RusthammerParserInputU16 () input cursor
      ⦃ result => Spec.unsignedIntegerOutcome .U16 input cursor result ⦄ := by
  exact complete_spec BeU16.Insts.RusthammerParserInputU16 () input cursor
    (Spec.unsignedIntegerOutcome .U16 input cursor) (be_u16_final_spec input cursor)

theorem be_u32_final_spec (input : Slice U8) (cursor : Cursor) :
    BeU32.Insts.RusthammerParserInputU32.parse_with () input cursor ParseContext.FINAL
      ⦃ result => Spec.completed (Spec.unsignedIntegerOutcome .U32 input cursor) result ⦄ := by
  simpa only [ParseContext.FINAL, Partial.primitive, Partial.primitiveResult, Spec.completed] using
    be_u32_with_spec input cursor .Final

theorem be_u32_spec (input : Slice U8) (cursor : Cursor) :
    Parser.parse.default BeU32.Insts.RusthammerParserInputU32 () input cursor
      ⦃ result => Spec.unsignedIntegerOutcome .U32 input cursor result ⦄ := by
  exact complete_spec BeU32.Insts.RusthammerParserInputU32 () input cursor
    (Spec.unsignedIntegerOutcome .U32 input cursor) (be_u32_final_spec input cursor)

theorem be_u64_final_spec (input : Slice U8) (cursor : Cursor) :
    BeU64.Insts.RusthammerParserInputU64.parse_with () input cursor ParseContext.FINAL
      ⦃ result => Spec.completed (Spec.unsignedIntegerOutcome .U64 input cursor) result ⦄ := by
  simpa only [ParseContext.FINAL, Partial.primitive, Partial.primitiveResult, Spec.completed] using
    be_u64_with_spec input cursor .Final

theorem be_u64_spec (input : Slice U8) (cursor : Cursor) :
    Parser.parse.default BeU64.Insts.RusthammerParserInputU64 () input cursor
      ⦃ result => Spec.unsignedIntegerOutcome .U64 input cursor result ⦄ := by
  exact complete_spec BeU64.Insts.RusthammerParserInputU64 () input cursor
    (Spec.unsignedIntegerOutcome .U64 input cursor) (be_u64_final_spec input cursor)

theorem i8_final_spec (input : Slice U8) (cursor : Cursor) :
    Code.I8.Insts.RusthammerParserInputI8.parse_with () input cursor ParseContext.FINAL
      ⦃ result => Spec.completed (Spec.signedIntegerOutcome .I8 input cursor) result ⦄ := by
  simpa only [ParseContext.FINAL, Partial.primitive, Partial.primitiveResult, Spec.completed] using
    i8_with_spec input cursor .Final

theorem i8_spec (input : Slice U8) (cursor : Cursor) :
    Parser.parse.default Code.I8.Insts.RusthammerParserInputI8 () input cursor
      ⦃ result => Spec.signedIntegerOutcome .I8 input cursor result ⦄ := by
  exact complete_spec Code.I8.Insts.RusthammerParserInputI8 () input cursor
    (Spec.signedIntegerOutcome .I8 input cursor) (i8_final_spec input cursor)

theorem be_i16_final_spec (input : Slice U8) (cursor : Cursor) :
    BeI16.Insts.RusthammerParserInputI16.parse_with () input cursor ParseContext.FINAL
      ⦃ result => Spec.completed (Spec.signedIntegerOutcome .I16 input cursor) result ⦄ := by
  simpa only [ParseContext.FINAL, Partial.primitive, Partial.primitiveResult, Spec.completed] using
    be_i16_with_spec input cursor .Final

theorem be_i16_spec (input : Slice U8) (cursor : Cursor) :
    Parser.parse.default BeI16.Insts.RusthammerParserInputI16 () input cursor
      ⦃ result => Spec.signedIntegerOutcome .I16 input cursor result ⦄ := by
  exact complete_spec BeI16.Insts.RusthammerParserInputI16 () input cursor
    (Spec.signedIntegerOutcome .I16 input cursor) (be_i16_final_spec input cursor)

theorem be_i32_final_spec (input : Slice U8) (cursor : Cursor) :
    BeI32.Insts.RusthammerParserInputI32.parse_with () input cursor ParseContext.FINAL
      ⦃ result => Spec.completed (Spec.signedIntegerOutcome .I32 input cursor) result ⦄ := by
  simpa only [ParseContext.FINAL, Partial.primitive, Partial.primitiveResult, Spec.completed] using
    be_i32_with_spec input cursor .Final

theorem be_i32_spec (input : Slice U8) (cursor : Cursor) :
    Parser.parse.default BeI32.Insts.RusthammerParserInputI32 () input cursor
      ⦃ result => Spec.signedIntegerOutcome .I32 input cursor result ⦄ := by
  exact complete_spec BeI32.Insts.RusthammerParserInputI32 () input cursor
    (Spec.signedIntegerOutcome .I32 input cursor) (be_i32_final_spec input cursor)

theorem be_i64_final_spec (input : Slice U8) (cursor : Cursor) :
    BeI64.Insts.RusthammerParserInputI64.parse_with () input cursor ParseContext.FINAL
      ⦃ result => Spec.completed (Spec.signedIntegerOutcome .I64 input cursor) result ⦄ := by
  simpa only [ParseContext.FINAL, Partial.primitive, Partial.primitiveResult, Spec.completed] using
    be_i64_with_spec input cursor .Final

theorem be_i64_spec (input : Slice U8) (cursor : Cursor) :
    Parser.parse.default BeI64.Insts.RusthammerParserInputI64 () input cursor
      ⦃ result => Spec.signedIntegerOutcome .I64 input cursor result ⦄ := by
  exact complete_spec BeI64.Insts.RusthammerParserInputI64 () input cursor
    (Spec.signedIntegerOutcome .I64 input cursor) (be_i64_final_spec input cursor)

end RustHammer.Proofs
