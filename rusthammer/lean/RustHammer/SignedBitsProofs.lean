import RustHammer.SignedBitsSpec
import RustHammer.PartialProofs

open Aeneas Aeneas.Std Result WP

namespace RustHammer.Proofs
open Code

theorem signed_bits_new_spec (width : U8) :
    SignedBits.new width ⦃ result => Spec.signedBitsNewOutcome width result ⦄ := by
  unfold SignedBits.new
  step with bits_new_spec width as ⟨result, hresult⟩
  by_cases hw : width.val ≤ 64
  · simp only [Spec.bitsNewOutcome, if_pos hw] at hresult
    simp [hresult, Spec.signedBitsNewOutcome, hw, spec_ok]
  · simp only [Spec.bitsNewOutcome, if_neg hw] at hresult
    simp [hresult, Spec.signedBitsNewOutcome, hw, spec_ok]

theorem signed_bits_new_valid (width : U8) (parser : SignedBits)
    (hnew : SignedBits.new width = ok (.Ok parser)) : Spec.validSignedBits parser := by
  have h := signed_bits_new_spec width
  rw [hnew] at h
  simp only [spec_ok, Spec.signedBitsNewOutcome] at h
  split at h
  · cases h
    assumption
  · cases h

theorem signed_bits_width_spec (parser : SignedBits) :
    SignedBits.width parser ⦃ result => result = parser.bits.width ⦄ := by
  exact bits_width_spec parser.bits

theorem signed_bits_clone_spec (parser : SignedBits) :
    SignedBits.Insts.CoreCloneClone.clone parser ⦃ result => result = parser ⦄ := by
  simp [SignedBits.Insts.CoreCloneClone.clone, spec_ok]

/-- Every intermediate is representable, including for the 64-bit minimum.
Both unsigned-to-signed casts preserve values rather than wrapping. -/
theorem sign_extend_spec (value : U64) (width : U8)
    (hwidth : width.val ≤ 64) (hfit : value.val < 2 ^ width.val) :
    sign_extend value width ⦃ result => result.val = Spec.signedValue width.val value.val ⦄ := by
  unfold sign_extend
  by_cases hz : width = 0#u8
  · simp [hz, Spec.signedValue, spec_ok]
  · have hpositive : 0 < width.val := by scalar_tac
    have hnonzero : width.val ≠ 0 := by omega
    simp only [hz, ↓reduceIte]
    step as ⟨shift, hshift⟩
    step as ⟨sign, hsign, _hsignBv⟩
    have hshiftBound : shift.val < 64 := by omega
    have hpowBound : 2 ^ shift.val < U64.size := by
      simp only [U64.size, U64.numBits]
      exact Nat.pow_lt_pow_right (by omega) hshiftBound
    have hsignShift : sign.val = 2 ^ shift.val := by
      simpa [Nat.one_shiftLeft, Nat.mod_eq_of_lt hpowBound] using hsign
    have hsignValue : sign.val = 2 ^ (width.val - 1) := by
      simpa only [hshift] using hsignShift
    have hsignPositive : 0 < sign.val := by rw [hsignValue]; positivity
    have hsignBound : sign.val ≤ 2 ^ 63 := by
      rw [hsignValue]
      exact Nat.pow_le_pow_right (by omega) (by omega)
    have hpower : 2 ^ width.val = sign.val * 2 := by
      rw [hsignValue, ← Nat.pow_succ]
      congr 1
      omega
    by_cases hbelow : value < sign
    · have hsmall : value.val < 2 ^ (width.val - 1) := by scalar_tac
      simp only [hbelow, ↓reduceIte, Spec.signedValue, if_neg hnonzero, if_pos hsmall]
      exact UScalar.hcast_inBounds_spec .I64 value (by scalar_tac)
    · have hlarge : ¬value.val < 2 ^ (width.val - 1) := by scalar_tac
      simp only [hbelow, ↓reduceIte]
      step as ⟨lower, hlower⟩
      step as ⟨upper, hupper⟩
      step as ⟨complement, hcomplement⟩
      step with UScalar.hcast_inBounds_spec .I64 complement (by scalar_tac) as ⟨signed, hsigned⟩
      step as ⟨result, hresult⟩
      simp only [Spec.signedValue, if_neg hnonzero, if_neg hlarge]
      omega

private theorem primitive_ok {α : Type} (status : InputStatus) (next : Cursor) (value : α) :
    Partial.primitiveResult status (.Ok (next, value)) = .Success next value := by
  cases status <;> rfl

/-- Total signed decoding reuses the unsigned field's safety and termination proof. -/
theorem signed_bits_with_spec (parser : SignedBits) (input : Slice U8) (cursor : Cursor)
    (status : InputStatus) (hconfig : Spec.validSignedBits parser) :
    SignedBits.Insts.RusthammerParserInputI64.parse_with parser input cursor (Spec.defaultContext status)
      ⦃ result => Partial.primitive status (Spec.signedBitsOutcome input cursor parser.bits.width) result ⦄ := by
  rw [SignedBits.Insts.RusthammerParserInputI64.parse_with_eq]
  step with bits_with_spec parser.bits input cursor status hconfig as ⟨outcome, houtcome⟩
  rcases houtcome with ⟨parsed, hparsed, rfl⟩
  by_cases hvalid : Spec.validCursor input cursor
  · by_cases hfit : Spec.position cursor + parser.bits.width.val ≤ 8 * input.val.length
    · simp only [Spec.bitsOutcome, if_pos hvalid, if_pos hfit] at hparsed
      rcases hparsed with ⟨next, value, rfl, hnext, hpos, hvalue⟩
      rw [primitive_ok]
      step with sign_extend_spec value parser.bits.width hconfig
        (by rw [hvalue]; exact unsignedBits_lt_pow _ _ _) as ⟨signed, hsigned⟩
      refine ⟨.Ok (next, signed), ?_, (primitive_ok status next signed).symm⟩
      simp only [Spec.signedBitsOutcome, if_pos hvalid, if_pos hfit]
      exact ⟨next, signed, rfl, hnext, hpos, by simpa [hvalue] using hsigned⟩
    · have heq : parsed = .Err .UnexpectedEnd := by
        simpa only [Spec.bitsOutcome, if_pos hvalid, if_neg hfit] using hparsed
      subst parsed
      cases status <;> simp only [Partial.primitiveResult, Spec.completedResult, spec_ok]
      all_goals exact ⟨.Err .UnexpectedEnd,
        by simp only [Spec.signedBitsOutcome, if_pos hvalid, if_neg hfit], rfl⟩
  · have heq : parsed = .Err .InvalidCursor := by
      simpa only [Spec.bitsOutcome, if_neg hvalid] using hparsed
    subst parsed
    cases status <;> simp only [Partial.primitiveResult, Spec.completedResult, spec_ok]
    all_goals exact ⟨.Err .InvalidCursor,
      by simp only [Spec.signedBitsOutcome, if_neg hvalid], rfl⟩

theorem signed_bits_final_spec (parser : SignedBits) (input : Slice U8) (cursor : Cursor)
    (hconfig : Spec.validSignedBits parser) :
    SignedBits.Insts.RusthammerParserInputI64.parse_with parser input cursor ParseContext.FINAL
      ⦃ result => Spec.completed (Spec.signedBitsOutcome input cursor parser.bits.width) result ⦄ := by
  simpa only [ParseContext.FINAL, Partial.primitive, Partial.primitiveResult, Spec.completed] using
    signed_bits_with_spec parser input cursor .Final hconfig

theorem signed_bits_spec (parser : SignedBits) (input : Slice U8) (cursor : Cursor)
    (hconfig : Spec.validSignedBits parser) :
    DirectParser.parse SignedBits.Insts.RusthammerParserInputI64 parser input cursor
      ⦃ result => Spec.signedBitsOutcome input cursor parser.bits.width result ⦄ := by
  exact complete_spec SignedBits.Insts.RusthammerParserInputI64 parser input cursor
    (Spec.signedBitsOutcome input cursor parser.bits.width) (signed_bits_final_spec parser input cursor hconfig)

/-- Nonempty fields use precisely the signed range for their bit width. -/
theorem signed_value_bounds (width value : Nat) (hpositive : 0 < width) (hfit : value < 2 ^ width) :
    -((2 ^ (width - 1) : Nat) : Int) ≤ Spec.signedValue width value ∧
      Spec.signedValue width value < ((2 ^ (width - 1) : Nat) : Int) := by
  have hpower : 2 ^ width = 2 ^ (width - 1) * 2 := by
    rw [← Nat.pow_succ]
    congr 1
    omega
  have hsignPositive : 0 < (2 : Nat) ^ (width - 1) := by positivity
  simp only [Spec.signedValue, if_neg (by omega : width ≠ 0)]
  split <;> omega

end RustHammer.Proofs
