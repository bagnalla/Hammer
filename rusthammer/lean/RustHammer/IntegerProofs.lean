import RustHammer.IntegerSpec
import RustHammer.SignedBitsProofs
import RustHammer.ByteProofs

open RustHammer.Code.grammar.numeric
  RustHammer.Code.input_types

open Aeneas Aeneas.Std Result WP

namespace RustHammer.Proofs
open Code

/-- Shared proof for the unsigned readers' lossless casts and outcome propagation. -/
private theorem narrow_unsigned_spec (ty : UScalarTy) (width : U8)
    (input : Slice U8) (cursor : Cursor)
    (hwidth : width.val = ty.numBits) (hconfig : width.val ≤ 64) :
    (do
      let parsed ← Bits.Insts.RusthammerParser_traitsParserInputU64.parse_with { width } input cursor ByteOrder.Big
      match parsed with
      | .Ok pair =>
        let (next, value) := pair
        do
        let narrowed ← lift (UScalar.cast ty value)
        ok (core.result.Result.Ok (next, narrowed))
      | .Err error => ok (.Err error))
      ⦃ result => Contracts.primitive (Spec.unsignedIntegerOutcome ty input cursor) result ⦄ := by
  step with bits_with_spec { width } input cursor hconfig as ⟨outcome, houtcome⟩
  rcases houtcome with ⟨parsed, hparsed, heq⟩
  subst outcome
  by_cases hvalid : Spec.validCursor input cursor
  · by_cases hfit : Spec.position cursor + width.val ≤ 8 * input.val.length
    · simp only [Spec.bitsOutcome, if_pos hvalid, if_pos hfit] at hparsed
      rcases hparsed with ⟨next, value, rfl, hnext, hpos, hvalue⟩

      have hbound := unsignedBits_lt_pow input (Spec.position cursor) width.val
      have hinBounds : value.val ≤ UScalar.max ty := by
        rw [UScalar.max, ← hwidth]
        omega
      step with UScalar.cast_inBounds_spec ty value hinBounds as ⟨narrowed, hnarrowed⟩
      refine ⟨.Ok (next, narrowed), ?_, rfl⟩
      simp only [Spec.unsignedIntegerOutcome, if_pos hvalid, ← hwidth, if_pos hfit,
        Spec.unsignedIntegerSuccess]
      exact ⟨next, narrowed, rfl, hnext, by simpa [hwidth] using hpos,
        by simpa [hnarrowed, hwidth] using hvalue⟩
    · have heq : parsed = .Err .UnexpectedEnd := by
        simpa only [Spec.bitsOutcome, if_pos hvalid, if_neg hfit] using hparsed
      subst parsed
      simp only [spec_ok]
      all_goals exact ⟨.Err .UnexpectedEnd,
        by simp only [Spec.unsignedIntegerOutcome, if_pos hvalid, ← hwidth, if_neg hfit], rfl⟩
  · have heq : parsed = .Err .InvalidCursor := by
      simpa only [Spec.bitsOutcome, if_neg hvalid] using hparsed
    subst parsed
    simp only [spec_ok]
    all_goals exact ⟨.Err .InvalidCursor,
      by simp only [Spec.unsignedIntegerOutcome, if_neg hvalid], rfl⟩

/-- Signed field bounds justify native signed narrowing, including each minimum. -/
private theorem narrow_signed_spec (ty : IScalarTy) (width : U8)
    (input : Slice U8) (cursor : Cursor)
    (hwidth : width.val = ty.numBits) (hconfig : width.val ≤ 64) :
    (do
      let parsed ← SignedBits.Insts.RusthammerParser_traitsParserInputI64.parse_with
        { bits := { width } } input cursor ByteOrder.Big
      match parsed with
      | .Ok pair =>
        let (next, value) := pair
        do
        let narrowed ← lift (IScalar.cast ty value)
        ok (core.result.Result.Ok (next, narrowed))
      | .Err error => ok (.Err error))
      ⦃ result => Contracts.primitive (Spec.signedIntegerOutcome ty input cursor) result ⦄ := by
  step with signed_bits_with_spec { bits := { width } } input cursor hconfig
    as ⟨outcome, houtcome⟩
  rcases houtcome with ⟨parsed, hparsed, heq⟩
  subst outcome
  by_cases hvalid : Spec.validCursor input cursor
  · by_cases hfit : Spec.position cursor + width.val ≤ 8 * input.val.length
    · simp only [Spec.signedBitsOutcome, if_pos hvalid, if_pos hfit] at hparsed
      rcases hparsed with ⟨next, value, rfl, hnext, hpos, hvalue⟩

      have hbound := signed_value_bounds width.val
        (Spec.unsignedBits input (Spec.position cursor) width.val)
        (by rw [hwidth]; exact Nat.pos_of_ne_zero (IScalarTy.numBits_nonzero ty))
        (unsignedBits_lt_pow input (Spec.position cursor) width.val)
      have hinBounds : IScalar.min ty ≤ value.val ∧ value.val ≤ IScalar.max ty := by
        simp only [Nat.cast_pow, Nat.cast_ofNat] at hbound
        simp only [IScalar.min, IScalar.max, ← hwidth]
        omega
      step with IScalar.cast_inBounds_spec ty value hinBounds as ⟨narrowed, hnarrowed⟩
      refine ⟨.Ok (next, narrowed), ?_, rfl⟩
      simp only [Spec.signedIntegerOutcome, if_pos hvalid, ← hwidth, if_pos hfit,
        Spec.signedIntegerSuccess]
      exact ⟨next, narrowed, rfl, hnext, by simpa [hwidth] using hpos,
        by simpa [hnarrowed, hwidth] using hvalue⟩
    · have heq : parsed = .Err .UnexpectedEnd := by
        simpa only [Spec.signedBitsOutcome, if_pos hvalid, if_neg hfit] using hparsed
      subst parsed
      simp only [spec_ok]
      all_goals exact ⟨.Err .UnexpectedEnd,
        by simp only [Spec.signedIntegerOutcome, if_pos hvalid, ← hwidth, if_neg hfit], rfl⟩
  · have heq : parsed = .Err .InvalidCursor := by
      simpa only [Spec.signedBitsOutcome, if_neg hvalid] using hparsed
    subst parsed
    simp only [spec_ok]
    all_goals exact ⟨.Err .InvalidCursor,
      by simp only [Spec.signedIntegerOutcome, if_neg hvalid], rfl⟩

theorem be_u16_with_spec (input : Slice U8) (cursor : Cursor) :
    BeU16.Insts.RusthammerParser_traitsParserInputU16.parse_with () input cursor ByteOrder.Big
      ⦃ result => Contracts.primitive (Spec.unsignedIntegerOutcome .U16 input cursor) result ⦄ := by
  rw [BeU16.Insts.RusthammerParser_traitsParserInputU16.parse_with]
  exact narrow_unsigned_spec .U16 16#u8 input cursor rfl (by decide)

theorem be_u32_with_spec (input : Slice U8) (cursor : Cursor) :
    BeU32.Insts.RusthammerParser_traitsParserInputU32.parse_with () input cursor ByteOrder.Big
      ⦃ result => Contracts.primitive (Spec.unsignedIntegerOutcome .U32 input cursor) result ⦄ := by
  rw [BeU32.Insts.RusthammerParser_traitsParserInputU32.parse_with]
  exact narrow_unsigned_spec .U32 32#u8 input cursor rfl (by decide)

theorem be_u64_with_spec (input : Slice U8) (cursor : Cursor) :
    BeU64.Insts.RusthammerParser_traitsParserInputU64.parse_with () input cursor ByteOrder.Big
      ⦃ result => Contracts.primitive (Spec.unsignedIntegerOutcome .U64 input cursor) result ⦄ := by
  rw [BeU64.Insts.RusthammerParser_traitsParserInputU64.parse_with]
  step with bits_with_spec { width := 64#u8 } input cursor (by decide) as ⟨outcome, houtcome⟩
  have h : Contracts.primitive (Spec.unsignedIntegerOutcome .U64 input cursor) outcome := by
    simpa only [Contracts.primitive, Spec.bitsOutcome, Spec.bitsSuccess, Spec.unsignedIntegerOutcome,
      Spec.unsignedIntegerSuccess, UScalar.ofNatCore_val_eq, UScalarTy.U64_numBits_eq] using houtcome
  cases outcome <;> simpa only [spec_ok] using h

theorem i8_with_spec (input : Slice U8) (cursor : Cursor) :
    Code.grammar.numeric.I8.Insts.RusthammerParser_traitsParserInputI8.parse_with () input cursor ByteOrder.Big
      ⦃ result => Contracts.primitive (Spec.signedIntegerOutcome .I8 input cursor) result ⦄ := by
  rw [Code.grammar.numeric.I8.Insts.RusthammerParser_traitsParserInputI8.parse_with]
  exact narrow_signed_spec .I8 8#u8 input cursor rfl (by decide)

theorem be_i16_with_spec (input : Slice U8) (cursor : Cursor) :
    BeI16.Insts.RusthammerParser_traitsParserInputI16.parse_with () input cursor ByteOrder.Big
      ⦃ result => Contracts.primitive (Spec.signedIntegerOutcome .I16 input cursor) result ⦄ := by
  rw [BeI16.Insts.RusthammerParser_traitsParserInputI16.parse_with]
  exact narrow_signed_spec .I16 16#u8 input cursor rfl (by decide)

theorem be_i32_with_spec (input : Slice U8) (cursor : Cursor) :
    BeI32.Insts.RusthammerParser_traitsParserInputI32.parse_with () input cursor ByteOrder.Big
      ⦃ result => Contracts.primitive (Spec.signedIntegerOutcome .I32 input cursor) result ⦄ := by
  rw [BeI32.Insts.RusthammerParser_traitsParserInputI32.parse_with]
  exact narrow_signed_spec .I32 32#u8 input cursor rfl (by decide)

theorem be_i64_with_spec (input : Slice U8) (cursor : Cursor) :
    BeI64.Insts.RusthammerParser_traitsParserInputI64.parse_with () input cursor ByteOrder.Big
      ⦃ result => Contracts.primitive (Spec.signedIntegerOutcome .I64 input cursor) result ⦄ := by
  rw [BeI64.Insts.RusthammerParser_traitsParserInputI64.parse_with]
  step with signed_bits_with_spec { bits := { width := 64#u8 } } input cursor (by decide)
    as ⟨outcome, houtcome⟩
  have h : Contracts.primitive (Spec.signedIntegerOutcome .I64 input cursor) outcome := by
    simpa only [Contracts.primitive, Spec.signedBitsOutcome, Spec.signedBitsSuccess, Spec.signedIntegerOutcome,
      Spec.signedIntegerSuccess, UScalar.ofNatCore_val_eq, IScalarTy.I64_numBits_eq] using houtcome
  cases outcome <;> simpa only [spec_ok] using h

/-- The existing byte reader is the unsigned eight-bit member of this family. -/
theorem byte_integer_with_spec (input : Slice U8) (cursor : Cursor) :
    Code.grammar.numeric.Byte.Insts.RusthammerParser_traitsParserInputU8.parse_with () input cursor ByteOrder.Big
      ⦃ result => Contracts.primitive (Spec.unsignedIntegerOutcome .U8 input cursor) result ⦄ := by
  simpa only [Contracts.primitive, Spec.byteOutcome, Spec.byteSuccess, Spec.unsignedIntegerOutcome,
    Spec.unsignedIntegerSuccess, UScalarTy.U8_numBits_eq] using byte_with_spec input cursor

theorem be_u16_final_spec (input : Slice U8) (cursor : Cursor) :
    BeU16.Insts.RusthammerParser_traitsParserInputU16.parse_with () input cursor ByteOrder.Big
      ⦃ result => Spec.satisfies (Spec.unsignedIntegerOutcome .U16 input cursor) result ⦄ := by
  simpa only [ByteOrder.Big, Contracts.primitive, Spec.satisfies] using
    be_u16_with_spec input cursor

theorem be_u16_spec (input : Slice U8) (cursor : Cursor) :
    parser_traits.Parser.parse.default BeU16.Insts.RusthammerParser_traitsParserInputU16 () input cursor
      ⦃ result => Spec.unsignedIntegerOutcome .U16 input cursor result ⦄ := by
  exact complete_spec BeU16.Insts.RusthammerParser_traitsParserInputU16 () input cursor
    (Spec.unsignedIntegerOutcome .U16 input cursor) (be_u16_final_spec input cursor)

theorem be_u32_final_spec (input : Slice U8) (cursor : Cursor) :
    BeU32.Insts.RusthammerParser_traitsParserInputU32.parse_with () input cursor ByteOrder.Big
      ⦃ result => Spec.satisfies (Spec.unsignedIntegerOutcome .U32 input cursor) result ⦄ := by
  simpa only [ByteOrder.Big, Contracts.primitive, Spec.satisfies] using
    be_u32_with_spec input cursor

theorem be_u32_spec (input : Slice U8) (cursor : Cursor) :
    parser_traits.Parser.parse.default BeU32.Insts.RusthammerParser_traitsParserInputU32 () input cursor
      ⦃ result => Spec.unsignedIntegerOutcome .U32 input cursor result ⦄ := by
  exact complete_spec BeU32.Insts.RusthammerParser_traitsParserInputU32 () input cursor
    (Spec.unsignedIntegerOutcome .U32 input cursor) (be_u32_final_spec input cursor)

theorem be_u64_final_spec (input : Slice U8) (cursor : Cursor) :
    BeU64.Insts.RusthammerParser_traitsParserInputU64.parse_with () input cursor ByteOrder.Big
      ⦃ result => Spec.satisfies (Spec.unsignedIntegerOutcome .U64 input cursor) result ⦄ := by
  simpa only [ByteOrder.Big, Contracts.primitive, Spec.satisfies] using
    be_u64_with_spec input cursor

theorem be_u64_spec (input : Slice U8) (cursor : Cursor) :
    parser_traits.Parser.parse.default BeU64.Insts.RusthammerParser_traitsParserInputU64 () input cursor
      ⦃ result => Spec.unsignedIntegerOutcome .U64 input cursor result ⦄ := by
  exact complete_spec BeU64.Insts.RusthammerParser_traitsParserInputU64 () input cursor
    (Spec.unsignedIntegerOutcome .U64 input cursor) (be_u64_final_spec input cursor)

theorem i8_final_spec (input : Slice U8) (cursor : Cursor) :
    Code.grammar.numeric.I8.Insts.RusthammerParser_traitsParserInputI8.parse_with () input cursor ByteOrder.Big
      ⦃ result => Spec.satisfies (Spec.signedIntegerOutcome .I8 input cursor) result ⦄ := by
  simpa only [ByteOrder.Big, Contracts.primitive, Spec.satisfies] using
    i8_with_spec input cursor

theorem i8_spec (input : Slice U8) (cursor : Cursor) :
    parser_traits.Parser.parse.default Code.grammar.numeric.I8.Insts.RusthammerParser_traitsParserInputI8 () input cursor
      ⦃ result => Spec.signedIntegerOutcome .I8 input cursor result ⦄ := by
  exact complete_spec Code.grammar.numeric.I8.Insts.RusthammerParser_traitsParserInputI8 () input cursor
    (Spec.signedIntegerOutcome .I8 input cursor) (i8_final_spec input cursor)

theorem be_i16_final_spec (input : Slice U8) (cursor : Cursor) :
    BeI16.Insts.RusthammerParser_traitsParserInputI16.parse_with () input cursor ByteOrder.Big
      ⦃ result => Spec.satisfies (Spec.signedIntegerOutcome .I16 input cursor) result ⦄ := by
  simpa only [ByteOrder.Big, Contracts.primitive, Spec.satisfies] using
    be_i16_with_spec input cursor

theorem be_i16_spec (input : Slice U8) (cursor : Cursor) :
    parser_traits.Parser.parse.default BeI16.Insts.RusthammerParser_traitsParserInputI16 () input cursor
      ⦃ result => Spec.signedIntegerOutcome .I16 input cursor result ⦄ := by
  exact complete_spec BeI16.Insts.RusthammerParser_traitsParserInputI16 () input cursor
    (Spec.signedIntegerOutcome .I16 input cursor) (be_i16_final_spec input cursor)

theorem be_i32_final_spec (input : Slice U8) (cursor : Cursor) :
    BeI32.Insts.RusthammerParser_traitsParserInputI32.parse_with () input cursor ByteOrder.Big
      ⦃ result => Spec.satisfies (Spec.signedIntegerOutcome .I32 input cursor) result ⦄ := by
  simpa only [ByteOrder.Big, Contracts.primitive, Spec.satisfies] using
    be_i32_with_spec input cursor

theorem be_i32_spec (input : Slice U8) (cursor : Cursor) :
    parser_traits.Parser.parse.default BeI32.Insts.RusthammerParser_traitsParserInputI32 () input cursor
      ⦃ result => Spec.signedIntegerOutcome .I32 input cursor result ⦄ := by
  exact complete_spec BeI32.Insts.RusthammerParser_traitsParserInputI32 () input cursor
    (Spec.signedIntegerOutcome .I32 input cursor) (be_i32_final_spec input cursor)

theorem be_i64_final_spec (input : Slice U8) (cursor : Cursor) :
    BeI64.Insts.RusthammerParser_traitsParserInputI64.parse_with () input cursor ByteOrder.Big
      ⦃ result => Spec.satisfies (Spec.signedIntegerOutcome .I64 input cursor) result ⦄ := by
  simpa only [ByteOrder.Big, Contracts.primitive, Spec.satisfies] using
    be_i64_with_spec input cursor

theorem be_i64_spec (input : Slice U8) (cursor : Cursor) :
    parser_traits.Parser.parse.default BeI64.Insts.RusthammerParser_traitsParserInputI64 () input cursor
      ⦃ result => Spec.signedIntegerOutcome .I64 input cursor result ⦄ := by
  exact complete_spec BeI64.Insts.RusthammerParser_traitsParserInputI64 () input cursor
    (Spec.signedIntegerOutcome .I64 input cursor) (be_i64_final_spec input cursor)

end RustHammer.Proofs
