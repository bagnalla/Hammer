import RustHammer.OrderParserSpec
import RustHammer.OrderScopeProofs
import RustHammer.IntegerProofs
import RustHammer.PositionProofs
import RustHammer.ByteSetProofs

open RustHammer.Code.grammar.bytes
  RustHammer.Code.grammar.numeric
  RustHammer.Code.grammar.position
  RustHammer.Code.input_types

open Aeneas Aeneas.Std Result WP

namespace RustHammer.Ordering
open Code Proofs

theorem bits_with_spec (parser : Bits) (input : Slice U8) (cursor : Cursor) (context : ByteOrder)
    (hw : Spec.validBits parser) :
    Bits.Insts.RusthammerParser_traitsParserInputU64.parse_with parser input cursor context
      ⦃ result => Contracts.primitive  (outcome input cursor parser.width context) result ⦄ := by
  rw [Bits.Insts.RusthammerParser_traitsParserInputU64.parse_with]
  step with read_ordered_bits_spec input cursor parser context hw as ⟨parsed, hp⟩
  exact ⟨parsed, hp, rfl⟩

theorem bit_with_spec (input : Slice U8) (cursor : Cursor) (context : ByteOrder) :
    Bit.Insts.RusthammerParser_traitsParserInputBool.parse_with () input cursor context
      ⦃ result => Contracts.primitive  (bitOutcome input cursor) result ⦄ := by
  exact Proofs.bit_with_spec input cursor

theorem literal_decode_spec (parser : Literal) (input : Slice U8) (cursor : Cursor) (order : ByteOrder)
    (hw : Spec.validLiteral parser) :
    read_literal input cursor parser order
      ⦃ result => literalOutcome input cursor parser.bits.width parser.value order result ⦄ := by
  unfold read_literal literalOutcome
  step with read_ordered_bits_spec input cursor parser.bits order hw.1 as ⟨numeric, hnumeric⟩
  cases numeric with
  | Err error =>
    simp only [spec_ok]
    exact ⟨.Err error, hnumeric, rfl⟩
  | Ok pair =>
    rcases pair with ⟨next, value⟩
    change ((if value = parser.value then ok (.Ok (next, value))
      else ok (.Err ParseError.Mismatch)) : Result (Spec.ParseResult U64))
      ⦃ result => ∃ numeric, outcome input cursor parser.bits.width order numeric ∧
        result = Spec.literalResult parser.value numeric ⦄
    by_cases heq : value = parser.value
    · simp only [heq, ↓reduceIte, spec_ok]
      exact ⟨.Ok (next, value), hnumeric, by simp [Spec.literalResult, heq]⟩
    · have hne : value.val ≠ parser.value.val := by scalar_tac
      simp only [heq, ↓reduceIte, spec_ok]
      exact ⟨.Ok (next, value), hnumeric, by simp [Spec.literalResult, hne]⟩

theorem literal_with_spec (parser : Literal) (input : Slice U8) (cursor : Cursor) (context : ByteOrder)
    (hw : Spec.validLiteral parser) :
    Literal.Insts.RusthammerParser_traitsParserInputU64.parse_with parser input cursor context
      ⦃ result => Contracts.primitive
        (literalOutcome input cursor parser.bits.width parser.value context) result ⦄ := by
  rw [Literal.Insts.RusthammerParser_traitsParserInputU64.parse_with]
  step with literal_decode_spec parser input cursor context hw as ⟨parsed, hp⟩
  exact ⟨parsed, hp, rfl⟩

/-- These primitives depend only on the input position, regardless of byte order. -/
theorem take_aligned_with_spec (parser : TakeAligned) (input : Slice U8) (cursor : Cursor)
    (context : ByteOrder) :
    TakeAligned.Insts.RusthammerParser_traitsParserInputSharedInputSliceU8.parse_with parser input cursor context
      ⦃ result => Contracts.primitive  (Spec.takeAlignedOutcome input cursor parser.count) result ⦄ := by
  exact Proofs.take_aligned_with_spec parser input cursor

theorem skip_bits_with_spec (parser : SkipBits) (input : Slice U8) (cursor : Cursor)
    (context : ByteOrder) :
    SkipBits.Insts.RusthammerParser_traitsParserInputTuple.parse_with parser input cursor context
      ⦃ result => Contracts.primitive  (Spec.skipBitsOutcome input cursor parser.bits) result ⦄ := by
  exact Proofs.skip_bits_with_spec parser input cursor

theorem tell_with_spec (input : Slice U8) (cursor : Cursor) (context : ByteOrder) :
    Tell.Insts.RusthammerParser_traitsParserInputCursor.parse_with () input cursor context
      ⦃ result => Spec.satisfies (Spec.tellOutcome input cursor) result ⦄ := by
  exact Proofs.tell_with_spec input cursor

theorem end_with_spec (input : Slice U8) (cursor : Cursor) (context : ByteOrder) :
    End.Insts.RusthammerParser_traitsParserInputTuple.parse_with () input cursor context
      ⦃ result => Contracts.endOutcome input cursor  result ⦄ := by
  exact Proofs.end_with_spec input cursor

theorem signed_bits_with_spec (parser : SignedBits) (input : Slice U8) (cursor : Cursor)
    (context : ByteOrder) (hconfig : Spec.validSignedBits parser) :
    SignedBits.Insts.RusthammerParser_traitsParserInputI64.parse_with parser input cursor context
      ⦃ result => Contracts.primitive  (signedBitsOutcome input cursor parser.bits.width context) result ⦄ := by
  rw [SignedBits.Insts.RusthammerParser_traitsParserInputI64.parse_with]
  step with bits_with_spec parser.bits input cursor context hconfig as ⟨outcome, houtcome⟩
  rcases houtcome with ⟨parsed, hparsed, heq⟩
  subst outcome
  by_cases hvalid : Spec.validCursor input cursor
  · by_cases hfit : Spec.position cursor + parser.bits.width.val ≤ 8 * input.val.length
    · simp only [Ordering.outcome, if_pos hvalid, if_pos hfit] at hparsed
      rcases hparsed with ⟨next, value, rfl, hnext, hpos, hvalue⟩

      step with sign_extend_spec value parser.bits.width hconfig
        (by rw [hvalue]; exact unsigned_bound _ _ _ _) as ⟨signed, hsigned⟩
      refine ⟨.Ok (next, signed), ?_, rfl⟩
      simp only [signedBitsOutcome, if_pos hvalid, if_pos hfit]
      exact ⟨next, signed, rfl, hnext, hpos, by simpa [hvalue] using hsigned⟩
    · have heq : parsed = .Err .UnexpectedEnd := by
        simpa only [Ordering.outcome, if_pos hvalid, if_neg hfit] using hparsed
      subst parsed
      simp only [spec_ok]
      all_goals exact ⟨.Err .UnexpectedEnd,
        by simp only [signedBitsOutcome, if_pos hvalid, if_neg hfit], rfl⟩
  · have heq : parsed = .Err .InvalidCursor := by
      simpa only [Ordering.outcome, if_neg hvalid] using hparsed
    subst parsed
    simp only [spec_ok]
    all_goals exact ⟨.Err .InvalidCursor,
      by simp only [signedBitsOutcome, if_neg hvalid], rfl⟩

private theorem narrow_unsigned_spec (ty : UScalarTy) (width : U8)
    (input : Slice U8) (cursor : Cursor) (context : ByteOrder)
    (hwidth : width.val = ty.numBits) (hconfig : width.val ≤ 64) :
    (do
      let parsed ← Bits.Insts.RusthammerParser_traitsParserInputU64.parse_with { width } input cursor context
      match parsed with
      | .Ok pair =>
        let (next, value) := pair
        do
        let narrowed ← lift (UScalar.cast ty value)
        ok (core.result.Result.Ok (next, narrowed))
      | .Err error => ok (.Err error))
      ⦃ result => Contracts.primitive  (unsignedIntegerOutcome ty input cursor context) result ⦄ := by
  step with bits_with_spec { width } input cursor context hconfig as ⟨outcome, houtcome⟩
  rcases houtcome with ⟨parsed, hparsed, heq⟩
  subst outcome
  by_cases hvalid : Spec.validCursor input cursor
  · by_cases hfit : Spec.position cursor + width.val ≤ 8 * input.val.length
    · simp only [Ordering.outcome, if_pos hvalid, if_pos hfit] at hparsed
      rcases hparsed with ⟨next, value, rfl, hnext, hpos, hvalue⟩

      have hbound := unsigned_bound input context (Spec.position cursor) width.val
      have hinBounds : value.val ≤ UScalar.max ty := by
        rw [UScalar.max, ← hwidth]
        omega
      step with UScalar.cast_inBounds_spec ty value hinBounds as ⟨narrowed, hnarrowed⟩
      refine ⟨.Ok (next, narrowed), ?_, rfl⟩
      simp only [unsignedIntegerOutcome, if_pos hvalid, ← hwidth, if_pos hfit,
        unsignedIntegerSuccess]
      exact ⟨next, narrowed, rfl, hnext, by simpa [hwidth] using hpos,
        by simpa [hnarrowed, hwidth] using hvalue⟩
    · have heq : parsed = .Err .UnexpectedEnd := by
        simpa only [Ordering.outcome, if_pos hvalid, if_neg hfit] using hparsed
      subst parsed
      simp only [spec_ok]
      all_goals exact ⟨.Err .UnexpectedEnd,
        by simp only [unsignedIntegerOutcome, if_pos hvalid, ← hwidth, if_neg hfit], rfl⟩
  · have heq : parsed = .Err .InvalidCursor := by
      simpa only [Ordering.outcome, if_neg hvalid] using hparsed
    subst parsed
    simp only [spec_ok]
    all_goals exact ⟨.Err .InvalidCursor,
      by simp only [unsignedIntegerOutcome, if_neg hvalid], rfl⟩

/-- Signed field bounds justify native signed narrowing, including each minimum. -/
private theorem narrow_signed_spec (ty : IScalarTy) (width : U8)
    (input : Slice U8) (cursor : Cursor) (context : ByteOrder)
    (hwidth : width.val = ty.numBits) (hconfig : width.val ≤ 64) :
    (do
      let parsed ← SignedBits.Insts.RusthammerParser_traitsParserInputI64.parse_with
        { bits := { width } } input cursor context
      match parsed with
      | .Ok pair =>
        let (next, value) := pair
        do
        let narrowed ← lift (IScalar.cast ty value)
        ok (core.result.Result.Ok (next, narrowed))
      | .Err error => ok (.Err error))
      ⦃ result => Contracts.primitive  (signedIntegerOutcome ty input cursor context) result ⦄ := by
  step with signed_bits_with_spec { bits := { width } } input cursor context hconfig
    as ⟨outcome, houtcome⟩
  rcases houtcome with ⟨parsed, hparsed, heq⟩
  subst outcome
  by_cases hvalid : Spec.validCursor input cursor
  · by_cases hfit : Spec.position cursor + width.val ≤ 8 * input.val.length
    · simp only [signedBitsOutcome, if_pos hvalid, if_pos hfit] at hparsed
      rcases hparsed with ⟨next, value, rfl, hnext, hpos, hvalue⟩

      have hbound := signed_value_bounds width.val
        (unsigned input context (Spec.position cursor) width.val)
        (by rw [hwidth]; exact Nat.pos_of_ne_zero (IScalarTy.numBits_nonzero ty))
        (unsigned_bound input context (Spec.position cursor) width.val)
      have hinBounds : IScalar.min ty ≤ value.val ∧ value.val ≤ IScalar.max ty := by
        simp only [Nat.cast_pow, Nat.cast_ofNat] at hbound
        simp only [IScalar.min, IScalar.max, ← hwidth]
        omega
      step with IScalar.cast_inBounds_spec ty value hinBounds as ⟨narrowed, hnarrowed⟩
      refine ⟨.Ok (next, narrowed), ?_, rfl⟩
      simp only [signedIntegerOutcome, if_pos hvalid, ← hwidth, if_pos hfit,
        signedIntegerSuccess]
      exact ⟨next, narrowed, rfl, hnext, by simpa [hwidth] using hpos,
        by simpa [hnarrowed, hwidth] using hvalue⟩
    · have heq : parsed = .Err .UnexpectedEnd := by
        simpa only [signedBitsOutcome, if_pos hvalid, if_neg hfit] using hparsed
      subst parsed
      simp only [spec_ok]
      all_goals exact ⟨.Err .UnexpectedEnd,
        by simp only [signedIntegerOutcome, if_pos hvalid, ← hwidth, if_neg hfit], rfl⟩
  · have heq : parsed = .Err .InvalidCursor := by
      simpa only [signedBitsOutcome, if_neg hvalid] using hparsed
    subst parsed
    simp only [spec_ok]
    all_goals exact ⟨.Err .InvalidCursor,
      by simp only [signedIntegerOutcome, if_neg hvalid], rfl⟩

theorem byte_with_spec (input : Slice U8) (cursor : Cursor) (context : ByteOrder) :
    Code.grammar.numeric.Byte.Insts.RusthammerParser_traitsParserInputU8.parse_with () input cursor context
      ⦃ result => Contracts.primitive
        (unsignedIntegerOutcome .U8 input cursor context) result ⦄ := by
  rw [Code.grammar.numeric.Byte.Insts.RusthammerParser_traitsParserInputU8.parse_with]
  exact narrow_unsigned_spec .U8 8#u8 input cursor context rfl (by decide)

theorem be_u16_with_spec (input : Slice U8) (cursor : Cursor) (context : ByteOrder) :
    BeU16.Insts.RusthammerParser_traitsParserInputU16.parse_with () input cursor context
      ⦃ result => Contracts.primitive
        (unsignedIntegerOutcome .U16 input cursor .Big) result ⦄ := by
  rw [BeU16.Insts.RusthammerParser_traitsParserInputU16.parse_with]
  exact narrow_unsigned_spec .U16 16#u8 input cursor .Big rfl (by decide)

theorem be_u32_with_spec (input : Slice U8) (cursor : Cursor) (context : ByteOrder) :
    BeU32.Insts.RusthammerParser_traitsParserInputU32.parse_with () input cursor context
      ⦃ result => Contracts.primitive
        (unsignedIntegerOutcome .U32 input cursor .Big) result ⦄ := by
  rw [BeU32.Insts.RusthammerParser_traitsParserInputU32.parse_with]
  exact narrow_unsigned_spec .U32 32#u8 input cursor .Big rfl (by decide)

theorem be_i16_with_spec (input : Slice U8) (cursor : Cursor) (context : ByteOrder) :
    BeI16.Insts.RusthammerParser_traitsParserInputI16.parse_with () input cursor context
      ⦃ result => Contracts.primitive
        (signedIntegerOutcome .I16 input cursor .Big) result ⦄ := by
  rw [BeI16.Insts.RusthammerParser_traitsParserInputI16.parse_with]
  exact narrow_signed_spec .I16 16#u8 input cursor .Big rfl (by decide)

theorem be_i32_with_spec (input : Slice U8) (cursor : Cursor) (context : ByteOrder) :
    BeI32.Insts.RusthammerParser_traitsParserInputI32.parse_with () input cursor context
      ⦃ result => Contracts.primitive
        (signedIntegerOutcome .I32 input cursor .Big) result ⦄ := by
  rw [BeI32.Insts.RusthammerParser_traitsParserInputI32.parse_with]
  exact narrow_signed_spec .I32 32#u8 input cursor .Big rfl (by decide)

theorem i8_with_spec (input : Slice U8) (cursor : Cursor) (context : ByteOrder) :
    Code.grammar.numeric.I8.Insts.RusthammerParser_traitsParserInputI8.parse_with () input cursor context
      ⦃ result => Contracts.primitive
        (signedIntegerOutcome .I8 input cursor context) result ⦄ := by
  rw [Code.grammar.numeric.I8.Insts.RusthammerParser_traitsParserInputI8.parse_with]
  exact narrow_signed_spec .I8 8#u8 input cursor context rfl (by decide)

theorem be_u64_with_spec (input : Slice U8) (cursor : Cursor) (context : ByteOrder) :
    BeU64.Insts.RusthammerParser_traitsParserInputU64.parse_with () input cursor context
      ⦃ result => Contracts.primitive  (unsignedIntegerOutcome .U64 input cursor .Big) result ⦄ := by
  rw [BeU64.Insts.RusthammerParser_traitsParserInputU64.parse_with]
  step with bits_with_spec { width := 64#u8 } input cursor .Big (by decide) as ⟨outcome, houtcome⟩
  have h : Contracts.primitive  (unsignedIntegerOutcome .U64 input cursor .Big) outcome := by
    simpa only [Contracts.primitive, Ordering.outcome, Ordering.success, unsignedIntegerOutcome,
      unsignedIntegerSuccess, UScalar.ofNatCore_val_eq, UScalarTy.U64_numBits_eq] using houtcome
  cases outcome <;> simpa only [spec_ok] using h

theorem be_i64_with_spec (input : Slice U8) (cursor : Cursor) (context : ByteOrder) :
    BeI64.Insts.RusthammerParser_traitsParserInputI64.parse_with () input cursor context
      ⦃ result => Contracts.primitive  (signedIntegerOutcome .I64 input cursor .Big) result ⦄ := by
  rw [BeI64.Insts.RusthammerParser_traitsParserInputI64.parse_with]
  step with signed_bits_with_spec { bits := { width := 64#u8 } } input cursor .Big (by decide)
    as ⟨outcome, houtcome⟩
  have h : Contracts.primitive  (signedIntegerOutcome .I64 input cursor .Big) outcome := by
    simpa only [Contracts.primitive, signedBitsOutcome, signedBitsSuccess, signedIntegerOutcome,
      signedIntegerSuccess, UScalar.ofNatCore_val_eq, IScalarTy.I64_numBits_eq] using houtcome
  cases outcome <;> simpa only [spec_ok] using h

/-- The existing byte reader is the unsigned eight-bit member of this family. -/
theorem match_byte_pattern_spec (pattern input : Slice U8) (cursor : Cursor) (context : ByteOrder) :
    grammar.bytes.match_byte_pattern pattern input cursor context
      ⦃ result => matchBytes input context pattern.val cursor result ⦄ := by
  rw [grammar.bytes.match_byte_pattern]
  unfold match_byte_pattern_loop
  apply loop.spec_decr_nat (fun state => pattern.val.length - state.2.val)
    (fun (next, index) => index.val ≤ pattern.val.length ∧
      ∀ outcome, matchBytes input context (pattern.val.drop index.val) next outcome →
        matchBytes input context pattern.val cursor outcome)
  · rintro ⟨next, index⟩ ⟨hindex, hcont⟩
    unfold match_byte_pattern_loop.body

    by_cases hlt : index < pattern.len
    · have hlen : index.val < pattern.val.length := by scalar_tac
      have hdrop : pattern.val.drop index.val =
          pattern.val[index.val] :: pattern.val.drop (index.val + 1) := by
        exact List.drop_eq_getElem_cons hlen
      simp only [hlt, ↓reduceIte]
      step with byte_with_spec input next context as ⟨decoded, hdecoded⟩
      cases decoded with
      | Err error =>
        simp only [spec_ok]
        apply hcont
        rw [hdrop]
        exact ⟨.Err error, hdecoded, rfl⟩
      | Ok pair =>
        rcases pair with ⟨after, value⟩
        step as ⟨expected, hexpected⟩
        by_cases heq : value = expected
        · simp only [heq, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
          step as ⟨following, hfollowing⟩
          refine ⟨by omega, ?_, by omega⟩
          intro outcome htail
          apply hcont
          rw [hdrop]
          refine ⟨.Ok (after, value), hdecoded, ?_⟩
          have hvalue : value = pattern.val[index.val] := by simpa [heq] using hexpected
          simpa only [hvalue, ↓reduceIte, hfollowing] using htail
        · simp only [bne_iff_ne, ne_eq, heq, not_false_eq_true, ↓reduceIte, spec_ok]
          apply hcont
          rw [hdrop]
          refine ⟨.Ok (after, value), hdecoded, ?_⟩
          have hvalue : value ≠ pattern.val[index.val] := by simpa [hexpected] using heq
          simp [hvalue]
    · have hend : index.val = pattern.val.length := by scalar_tac
      simp only [hlt, ↓reduceIte, spec_ok]
      apply hcont
      simp [hend, matchBytes]
  · simp

theorem byte_pattern_with_spec (parser : BytePattern) (input : Slice U8)
    (cursor : Cursor) (context : ByteOrder) :
    BytePattern.Insts.RusthammerParser_traitsParserInputSharedPatternSliceU8.parse_with parser input cursor context
      ⦃ result => bytePatternOutcome input context parser.pattern cursor result ⦄ := by
  rw [BytePattern.Insts.RusthammerParser_traitsParserInputSharedPatternSliceU8.parse_with]
  step with match_byte_pattern_spec parser.pattern input cursor context as ⟨outcome, houtcome⟩
  cases outcome with
  | Ok pair =>
    rcases pair with ⟨next, value⟩
    cases value
    simp only [bytePatternOutcome]
    exact ⟨rfl, houtcome⟩
  | Err error => simpa only [spec_ok, bytePatternOutcome] using houtcome

theorem byte_in_with_spec (parser : ByteIn) (input : Slice U8) (cursor : Cursor)
    (context : ByteOrder) :
    ByteIn.Insts.RusthammerParser_traitsParserInputU8.parse_with parser input cursor context
      ⦃ result => Contracts.verify
        (fun start => Contracts.primitive  (unsignedIntegerOutcome .U8 input start context))
        (Spec.bitmapPredicate parser.set false) cursor result ⦄ := by
  rw [ByteIn.Insts.RusthammerParser_traitsParserInputU8.parse_with]
  apply verify_with_spec Code.grammar.numeric.Byte.Insts.RusthammerParser_traitsParserInputU8
    ParserInputByteInU8.parse_with.closure.Insts.CoreOpsFunctionFnTupleShared1U8Bool
    { parser := (), predicate := parser } input cursor context _
    (Spec.bitmapPredicate parser.set false) (by
      simpa only [Code.grammar.numeric.Byte.Insts.RusthammerParser_traitsParserInputU8.parse_with] using
        byte_with_spec input cursor context)
  intro next value _
  exact byte_in_predicate_spec parser value

theorem byte_not_in_with_spec (parser : ByteNotIn) (input : Slice U8) (cursor : Cursor)
    (context : ByteOrder) :
    ByteNotIn.Insts.RusthammerParser_traitsParserInputU8.parse_with parser input cursor context
      ⦃ result => Contracts.verify
        (fun start => Contracts.primitive  (unsignedIntegerOutcome .U8 input start context))
        (Spec.bitmapPredicate parser.set true) cursor result ⦄ := by
  rw [ByteNotIn.Insts.RusthammerParser_traitsParserInputU8.parse_with]
  apply verify_with_spec Code.grammar.numeric.Byte.Insts.RusthammerParser_traitsParserInputU8
    ParserInputByteNotInU8.parse_with.closure.Insts.CoreOpsFunctionFnTupleShared1U8Bool
    { parser := (), predicate := parser } input cursor context _
    (Spec.bitmapPredicate parser.set true) (by
      simpa only [Code.grammar.numeric.Byte.Insts.RusthammerParser_traitsParserInputU8.parse_with] using
        byte_with_spec input cursor context)
  intro next value _
  exact byte_not_in_predicate_spec parser value

end RustHammer.Ordering
