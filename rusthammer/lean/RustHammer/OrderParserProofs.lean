import RustHammer.OrderParserSpec
import RustHammer.OrderScopeProofs
import RustHammer.IntegerProofs
import RustHammer.PositionProofs
import RustHammer.ByteSetProofs

open Aeneas Aeneas.Std Result WP

namespace RustHammer.Ordering
open Code Proofs

private theorem primitive_ok {α : Type} (status : InputStatus) (next : Cursor) (value : α) :
    Partial.primitiveResult status (.Ok (next, value)) = .Success next value := by
  cases status <;> rfl

theorem bits_with_spec (parser : Bits) (input : Slice U8) (cursor : Cursor) (context : ParseContext)
    (hw : Spec.validBits parser) :
    Bits.Insts.RusthammerParserInputU64.parse_with parser input cursor context
      ⦃ result => Partial.primitive context.status (outcome input cursor parser.width context.order) result ⦄ := by
  unfold Bits.Insts.RusthammerParserInputU64.parse_with
  step with read_ordered_bits_spec input cursor parser context.order hw as ⟨parsed, hp⟩
  step with classify_spec context.status parsed as ⟨result, hr⟩
  exact ⟨parsed, hp, hr⟩

theorem bit_with_spec (input : Slice U8) (cursor : Cursor) (context : ParseContext) :
    Bit.Insts.RusthammerParserInputBool.parse_with () input cursor context
      ⦃ result => Partial.primitive context.status (bitOutcome input cursor context.order.bit) result ⦄ := by
  unfold Bit.Insts.RusthammerParserInputBool.parse_with
  step with read_bit_ordered_spec input cursor context.order.bit as ⟨parsed, hp⟩
  step with classify_spec context.status parsed as ⟨result, hr⟩
  exact ⟨parsed, hp, hr⟩

theorem literal_decode_spec (parser : Literal) (input : Slice U8) (cursor : Cursor) (order : Order)
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

theorem literal_with_spec (parser : Literal) (input : Slice U8) (cursor : Cursor) (context : ParseContext)
    (hw : Spec.validLiteral parser) :
    Literal.Insts.RusthammerParserInputU64.parse_with parser input cursor context
      ⦃ result => Partial.primitive context.status
        (literalOutcome input cursor parser.bits.width parser.value context.order) result ⦄ := by
  unfold Literal.Insts.RusthammerParserInputU64.parse_with
  step with literal_decode_spec parser input cursor context.order hw as ⟨parsed, hp⟩
  step with classify_spec context.status parsed as ⟨result, hr⟩
  exact ⟨parsed, hp, hr⟩

/-- These primitives depend on finality or position, and preserve any ordering. -/
theorem take_aligned_with_spec (parser : TakeAligned) (input : Slice U8) (cursor : Cursor)
    (context : ParseContext) :
    TakeAligned.Insts.RusthammerParserInputSharedInputSliceU8.parse_with parser input cursor context
      ⦃ result => Partial.primitive context.status (Spec.takeAlignedOutcome input cursor parser.count) result ⦄ := by
  exact Proofs.take_aligned_with_spec parser input cursor context.status

theorem skip_bits_with_spec (parser : SkipBits) (input : Slice U8) (cursor : Cursor)
    (context : ParseContext) :
    SkipBits.Insts.RusthammerParserInputTuple.parse_with parser input cursor context
      ⦃ result => Partial.primitive context.status (Spec.skipBitsOutcome input cursor parser.bits) result ⦄ := by
  exact Proofs.skip_bits_with_spec parser input cursor context.status

theorem tell_with_spec (input : Slice U8) (cursor : Cursor) (context : ParseContext) :
    Tell.Insts.RusthammerParserInputCursor.parse_with () input cursor context
      ⦃ result => Spec.completed (Spec.tellOutcome input cursor) result ⦄ := by
  exact Proofs.tell_with_spec input cursor context.status

theorem end_with_spec (input : Slice U8) (cursor : Cursor) (context : ParseContext) :
    End.Insts.RusthammerParserInputTuple.parse_with () input cursor context
      ⦃ result => Partial.endOutcome input cursor context.status result ⦄ := by
  exact Proofs.end_with_spec input cursor context.status

theorem signed_bits_with_spec (parser : SignedBits) (input : Slice U8) (cursor : Cursor)
    (context : ParseContext) (hconfig : Spec.validSignedBits parser) :
    SignedBits.Insts.RusthammerParserInputI64.parse_with parser input cursor context
      ⦃ result => Partial.primitive context.status (signedBitsOutcome input cursor parser.bits.width context.order) result ⦄ := by
  unfold SignedBits.Insts.RusthammerParserInputI64.parse_with
  step with bits_with_spec parser.bits input cursor context hconfig as ⟨outcome, houtcome⟩
  rcases houtcome with ⟨parsed, hparsed, rfl⟩
  by_cases hvalid : Spec.validCursor input cursor
  · by_cases hfit : Spec.position cursor + parser.bits.width.val ≤ 8 * input.val.length
    · simp only [Ordering.outcome, if_pos hvalid, if_pos hfit] at hparsed
      rcases hparsed with ⟨next, value, rfl, hnext, hpos, hvalue⟩
      rw [primitive_ok]
      step with sign_extend_spec value parser.bits.width hconfig
        (by rw [hvalue]; exact unsigned_bound _ _ _ _) as ⟨signed, hsigned⟩
      refine ⟨.Ok (next, signed), ?_, (primitive_ok context.status next signed).symm⟩
      simp only [signedBitsOutcome, if_pos hvalid, if_pos hfit]
      exact ⟨next, signed, rfl, hnext, hpos, by simpa [hvalue] using hsigned⟩
    · have heq : parsed = .Err .UnexpectedEnd := by
        simpa only [Ordering.outcome, if_pos hvalid, if_neg hfit] using hparsed
      subst parsed
      cases hs : context.status <;> simp only [Partial.primitiveResult, Spec.completedResult, spec_ok]
      all_goals exact ⟨.Err .UnexpectedEnd,
        by simp only [signedBitsOutcome, if_pos hvalid, if_neg hfit], rfl⟩
  · have heq : parsed = .Err .InvalidCursor := by
      simpa only [Ordering.outcome, if_neg hvalid] using hparsed
    subst parsed
    cases hs : context.status <;> simp only [Partial.primitiveResult, Spec.completedResult, spec_ok]
    all_goals exact ⟨.Err .InvalidCursor,
      by simp only [signedBitsOutcome, if_neg hvalid], rfl⟩

private theorem narrow_unsigned_spec (ty : UScalarTy) (width : U8)
    (input : Slice U8) (cursor : Cursor) (context : ParseContext)
    (hwidth : width.val = ty.numBits) (hconfig : width.val ≤ 64) :
    (do
      let parsed ← Bits.Insts.RusthammerParserInputU64.parse_with { width } input cursor context
      match parsed with
      | .Success next value =>
        let narrowed ← lift (UScalar.cast ty value)
        ok (ParseOutcome.Success next narrowed)
      | .Error error => ok (.Error error)
      | .NeedMore => ok .NeedMore)
      ⦃ result => Partial.primitive context.status (unsignedIntegerOutcome ty input cursor context.order) result ⦄ := by
  step with bits_with_spec { width } input cursor context hconfig as ⟨outcome, houtcome⟩
  rcases houtcome with ⟨parsed, hparsed, rfl⟩
  by_cases hvalid : Spec.validCursor input cursor
  · by_cases hfit : Spec.position cursor + width.val ≤ 8 * input.val.length
    · simp only [Ordering.outcome, if_pos hvalid, if_pos hfit] at hparsed
      rcases hparsed with ⟨next, value, rfl, hnext, hpos, hvalue⟩
      rw [primitive_ok]
      have hbound := unsigned_bound input context.order (Spec.position cursor) width.val
      have hinBounds : value.val ≤ UScalar.max ty := by
        rw [UScalar.max, ← hwidth]
        omega
      step with UScalar.cast_inBounds_spec ty value hinBounds as ⟨narrowed, hnarrowed⟩
      refine ⟨.Ok (next, narrowed), ?_, (primitive_ok context.status next narrowed).symm⟩
      simp only [unsignedIntegerOutcome, if_pos hvalid, ← hwidth, if_pos hfit,
        unsignedIntegerSuccess]
      exact ⟨next, narrowed, rfl, hnext, by simpa [hwidth] using hpos,
        by simpa [hnarrowed, hwidth] using hvalue⟩
    · have heq : parsed = .Err .UnexpectedEnd := by
        simpa only [Ordering.outcome, if_pos hvalid, if_neg hfit] using hparsed
      subst parsed
      cases hs : context.status <;> simp only [Partial.primitiveResult, Spec.completedResult, spec_ok]
      all_goals exact ⟨.Err .UnexpectedEnd,
        by simp only [unsignedIntegerOutcome, if_pos hvalid, ← hwidth, if_neg hfit], rfl⟩
  · have heq : parsed = .Err .InvalidCursor := by
      simpa only [Ordering.outcome, if_neg hvalid] using hparsed
    subst parsed
    cases hs : context.status <;> simp only [Partial.primitiveResult, Spec.completedResult, spec_ok]
    all_goals exact ⟨.Err .InvalidCursor,
      by simp only [unsignedIntegerOutcome, if_neg hvalid], rfl⟩

/-- Signed field bounds justify native signed narrowing, including each minimum. -/
private theorem narrow_signed_spec (ty : IScalarTy) (width : U8)
    (input : Slice U8) (cursor : Cursor) (context : ParseContext)
    (hwidth : width.val = ty.numBits) (hconfig : width.val ≤ 64) :
    (do
      let parsed ← SignedBits.Insts.RusthammerParserInputI64.parse_with
        { bits := { width } } input cursor context
      match parsed with
      | .Success next value =>
        let narrowed ← lift (IScalar.cast ty value)
        ok (ParseOutcome.Success next narrowed)
      | .Error error => ok (.Error error)
      | .NeedMore => ok .NeedMore)
      ⦃ result => Partial.primitive context.status (signedIntegerOutcome ty input cursor context.order) result ⦄ := by
  step with signed_bits_with_spec { bits := { width } } input cursor context hconfig
    as ⟨outcome, houtcome⟩
  rcases houtcome with ⟨parsed, hparsed, rfl⟩
  by_cases hvalid : Spec.validCursor input cursor
  · by_cases hfit : Spec.position cursor + width.val ≤ 8 * input.val.length
    · simp only [signedBitsOutcome, if_pos hvalid, if_pos hfit] at hparsed
      rcases hparsed with ⟨next, value, rfl, hnext, hpos, hvalue⟩
      rw [primitive_ok]
      have hbound := signed_value_bounds width.val
        (unsigned input context.order (Spec.position cursor) width.val)
        (by rw [hwidth]; exact Nat.pos_of_ne_zero (IScalarTy.numBits_nonzero ty))
        (unsigned_bound input context.order (Spec.position cursor) width.val)
      have hinBounds : IScalar.min ty ≤ value.val ∧ value.val ≤ IScalar.max ty := by
        simp only [Nat.cast_pow, Nat.cast_ofNat] at hbound
        simp only [IScalar.min, IScalar.max, ← hwidth]
        omega
      step with IScalar.cast_inBounds_spec ty value hinBounds as ⟨narrowed, hnarrowed⟩
      refine ⟨.Ok (next, narrowed), ?_, (primitive_ok context.status next narrowed).symm⟩
      simp only [signedIntegerOutcome, if_pos hvalid, ← hwidth, if_pos hfit,
        signedIntegerSuccess]
      exact ⟨next, narrowed, rfl, hnext, by simpa [hwidth] using hpos,
        by simpa [hnarrowed, hwidth] using hvalue⟩
    · have heq : parsed = .Err .UnexpectedEnd := by
        simpa only [signedBitsOutcome, if_pos hvalid, if_neg hfit] using hparsed
      subst parsed
      cases hs : context.status <;> simp only [Partial.primitiveResult, Spec.completedResult, spec_ok]
      all_goals exact ⟨.Err .UnexpectedEnd,
        by simp only [signedIntegerOutcome, if_pos hvalid, ← hwidth, if_neg hfit], rfl⟩
  · have heq : parsed = .Err .InvalidCursor := by
      simpa only [signedBitsOutcome, if_neg hvalid] using hparsed
    subst parsed
    cases hs : context.status <;> simp only [Partial.primitiveResult, Spec.completedResult, spec_ok]
    all_goals exact ⟨.Err .InvalidCursor,
      by simp only [signedIntegerOutcome, if_neg hvalid], rfl⟩

theorem byte_with_spec (input : Slice U8) (cursor : Cursor) (context : ParseContext) :
    Byte.Insts.RusthammerParserInputU8.parse_with () input cursor context
      ⦃ result => Partial.primitive context.status
        (unsignedIntegerOutcome .U8 input cursor context.order) result ⦄ := by
  exact narrow_unsigned_spec .U8 8#u8 input cursor context rfl (by decide)

abbrev bigContext (context : ParseContext) : ParseContext :=
  { context with order := { bit := context.order.bit, byte := .Big } }

theorem be_u16_with_spec (input : Slice U8) (cursor : Cursor) (context : ParseContext) :
    BeU16.Insts.RusthammerParserInputU16.parse_with () input cursor context
      ⦃ result => Partial.primitive context.status
        (unsignedIntegerOutcome .U16 input cursor (bigContext context).order) result ⦄ := by
  exact narrow_unsigned_spec .U16 16#u8 input cursor (bigContext context) rfl (by decide)

theorem be_u32_with_spec (input : Slice U8) (cursor : Cursor) (context : ParseContext) :
    BeU32.Insts.RusthammerParserInputU32.parse_with () input cursor context
      ⦃ result => Partial.primitive context.status
        (unsignedIntegerOutcome .U32 input cursor (bigContext context).order) result ⦄ := by
  exact narrow_unsigned_spec .U32 32#u8 input cursor (bigContext context) rfl (by decide)

theorem be_i16_with_spec (input : Slice U8) (cursor : Cursor) (context : ParseContext) :
    BeI16.Insts.RusthammerParserInputI16.parse_with () input cursor context
      ⦃ result => Partial.primitive context.status
        (signedIntegerOutcome .I16 input cursor (bigContext context).order) result ⦄ := by
  exact narrow_signed_spec .I16 16#u8 input cursor (bigContext context) rfl (by decide)

theorem be_i32_with_spec (input : Slice U8) (cursor : Cursor) (context : ParseContext) :
    BeI32.Insts.RusthammerParserInputI32.parse_with () input cursor context
      ⦃ result => Partial.primitive context.status
        (signedIntegerOutcome .I32 input cursor (bigContext context).order) result ⦄ := by
  exact narrow_signed_spec .I32 32#u8 input cursor (bigContext context) rfl (by decide)

theorem i8_with_spec (input : Slice U8) (cursor : Cursor) (context : ParseContext) :
    I8.Insts.RusthammerParserInputI8.parse_with () input cursor context
      ⦃ result => Partial.primitive context.status
        (signedIntegerOutcome .I8 input cursor context.order) result ⦄ := by
  exact narrow_signed_spec .I8 8#u8 input cursor context rfl (by decide)

theorem be_u64_with_spec (input : Slice U8) (cursor : Cursor) (context : ParseContext) :
    BeU64.Insts.RusthammerParserInputU64.parse_with () input cursor context
      ⦃ result => Partial.primitive context.status (unsignedIntegerOutcome .U64 input cursor (bigContext context).order) result ⦄ := by
  unfold BeU64.Insts.RusthammerParserInputU64.parse_with
  step with bits_with_spec { width := 64#u8 } input cursor (bigContext context) (by decide) as ⟨outcome, houtcome⟩
  have h : Partial.primitive context.status (unsignedIntegerOutcome .U64 input cursor (bigContext context).order) outcome := by
    simpa only [Partial.primitive, Ordering.outcome, Ordering.success, unsignedIntegerOutcome,
      unsignedIntegerSuccess, UScalar.ofNatCore_val_eq, UScalarTy.U64_numBits_eq] using houtcome
  cases outcome <;> simpa only [spec_ok] using h

theorem be_i64_with_spec (input : Slice U8) (cursor : Cursor) (context : ParseContext) :
    BeI64.Insts.RusthammerParserInputI64.parse_with () input cursor context
      ⦃ result => Partial.primitive context.status (signedIntegerOutcome .I64 input cursor (bigContext context).order) result ⦄ := by
  unfold BeI64.Insts.RusthammerParserInputI64.parse_with
  step with signed_bits_with_spec { bits := { width := 64#u8 } } input cursor (bigContext context) (by decide)
    as ⟨outcome, houtcome⟩
  have h : Partial.primitive context.status (signedIntegerOutcome .I64 input cursor (bigContext context).order) outcome := by
    simpa only [Partial.primitive, signedBitsOutcome, signedBitsSuccess, signedIntegerOutcome,
      signedIntegerSuccess, UScalar.ofNatCore_val_eq, IScalarTy.I64_numBits_eq] using houtcome
  cases outcome <;> simpa only [spec_ok] using h

/-- The existing byte reader is the unsigned eight-bit member of this family. -/
theorem match_byte_pattern_spec (pattern input : Slice U8) (cursor : Cursor) (context : ParseContext) :
    match_byte_pattern pattern input cursor context
      ⦃ result => matchBytes input context pattern.val cursor result ⦄ := by
  unfold match_byte_pattern match_byte_pattern_loop
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
      | NeedMore =>
        simp only [spec_ok]
        apply hcont
        rw [hdrop]
        exact ⟨.NeedMore, hdecoded, rfl⟩
      | Error error =>
        simp only [spec_ok]
        apply hcont
        rw [hdrop]
        exact ⟨.Error error, hdecoded, rfl⟩
      | Success after value =>
        step as ⟨expected, hexpected⟩
        by_cases heq : value = expected
        · simp only [heq, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
          step as ⟨following, hfollowing⟩
          refine ⟨by omega, ?_, by omega⟩
          intro outcome htail
          apply hcont
          rw [hdrop]
          refine ⟨.Success after value, hdecoded, ?_⟩
          have hvalue : value = pattern.val[index.val] := by simpa [heq] using hexpected
          simpa only [hvalue, ↓reduceIte, hfollowing] using htail
        · simp only [bne_iff_ne, ne_eq, heq, not_false_eq_true, ↓reduceIte, spec_ok]
          apply hcont
          rw [hdrop]
          refine ⟨.Success after value, hdecoded, ?_⟩
          have hvalue : value ≠ pattern.val[index.val] := by simpa [hexpected] using heq
          simp [hvalue]
    · have hend : index.val = pattern.val.length := by scalar_tac
      simp only [hlt, ↓reduceIte, spec_ok]
      apply hcont
      simp [hend, matchBytes]
  · simp

theorem byte_pattern_with_spec (parser : BytePattern) (input : Slice U8)
    (cursor : Cursor) (context : ParseContext) :
    BytePattern.Insts.RusthammerParserInputSharedPatternSliceU8.parse_with parser input cursor context
      ⦃ result => bytePatternOutcome input context parser.pattern cursor result ⦄ := by
  unfold BytePattern.Insts.RusthammerParserInputSharedPatternSliceU8.parse_with
  step with match_byte_pattern_spec parser.pattern input cursor context as ⟨outcome, houtcome⟩
  cases outcome <;> simp only [spec_ok, bytePatternOutcome]
  · exact ⟨trivial, houtcome⟩
  · exact houtcome
  · exact houtcome

theorem byte_in_with_spec (parser : ByteIn) (input : Slice U8) (cursor : Cursor)
    (context : ParseContext) :
    ByteIn.Insts.RusthammerParserInputU8.parse_with parser input cursor context
      ⦃ result => Partial.verify
        (fun start => Partial.primitive context.status (unsignedIntegerOutcome .U8 input start context.order))
        (Spec.bitmapPredicate parser.set false) cursor result ⦄ := by
  unfold ByteIn.Insts.RusthammerParserInputU8.parse_with
  apply verify_with_spec Byte.Insts.RusthammerParserInputU8
    ParserInputByteInU8.parse_with.closure.Insts.CoreOpsFunctionFnTupleShared1U8Bool
    { parser := (), predicate := parser } input cursor context _
    (Spec.bitmapPredicate parser.set false) (byte_with_spec input cursor context)
  intro next value _
  exact byte_in_predicate_spec parser value

theorem byte_not_in_with_spec (parser : ByteNotIn) (input : Slice U8) (cursor : Cursor)
    (context : ParseContext) :
    ByteNotIn.Insts.RusthammerParserInputU8.parse_with parser input cursor context
      ⦃ result => Partial.verify
        (fun start => Partial.primitive context.status (unsignedIntegerOutcome .U8 input start context.order))
        (Spec.bitmapPredicate parser.set true) cursor result ⦄ := by
  unfold ByteNotIn.Insts.RusthammerParserInputU8.parse_with
  apply verify_with_spec Byte.Insts.RusthammerParserInputU8
    ParserInputByteNotInU8.parse_with.closure.Insts.CoreOpsFunctionFnTupleShared1U8Bool
    { parser := (), predicate := parser } input cursor context _
    (Spec.bitmapPredicate parser.set true) (byte_with_spec input cursor context)
  intro next value _
  exact byte_not_in_predicate_spec parser value

end RustHammer.Ordering
