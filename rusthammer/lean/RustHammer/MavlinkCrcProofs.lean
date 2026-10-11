import RustHammer.MavlinkCrcSpec

open Aeneas Aeneas.Std Result WP

namespace RustHammer.Mavlink
open Code.mavlink_example

private theorem crc_bit_test (word : BitVec 16) :
    ((word &&& 1#16) != 0#16) = word.getLsbD 0 := by
  rw [BitVec.and_one_eq_setWidth_ofBool_getLsbD]
  cases word.getLsbD 0 <;> decide

theorem crc_rounds_spec (initial : U16) (start : U8) (hstart : start.val ≤ 8) :
    crc_accumulate_loop initial start
      ⦃ result => result.bv = crcRounds (8 - start.val) initial.bv ⦄ := by
  unfold crc_accumulate_loop
  apply loop.spec_decr_nat (fun state => 8 - state.2.val)
    (fun (word, bit) => bit.val ≤ 8 ∧
      crcRounds (8 - bit.val) word.bv = crcRounds (8 - start.val) initial.bv)
  · rintro ⟨word, bit⟩ ⟨hbit, hresult⟩
    unfold crc_accumulate_loop.body
    by_cases hlt : bit < 8#u8
    · have hlt' : bit.val < 8 := by scalar_tac
      simp only [hlt, ↓reduceIte]
      step as ⟨low, _, hlow⟩
      have htest : (low != 0#u16) = word.bv.getLsbD 0 := by
        have heq : low = (⟨word.bv &&& 1#16⟩ : U16) := by
          apply U16.bv_eq_imp_eq
          simpa using hlow
        subst low
        apply Bool.eq_iff_iff.mpr
        simpa only [bne_iff_ne, ne_eq, UScalar.eq_equiv_bv_eq, U16.ofNat_bv,
          UScalarTy.numBits] using
          Bool.eq_iff_iff.mp (crc_bit_test word.bv)
      have hshift : (word >>> 1#i32) = ok (⟨word.bv >>> 1⟩ : U16) := by
        rfl
      simp only [hshift, bind_ok, htest]
      by_cases hfeedback : word.bv.getLsbD 0 = true
      · simp only [hfeedback, ↓reduceIte, bind_ok]
        step as ⟨next, hnext⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        have hn : 8 - bit.val = (8 - next.val) + 1 := by scalar_tac
        change crcRounds (8 - next.val) ((word.bv >>> 1) ^^^ 33800#16) = _
        rw [hn, crcRounds, crcBit, if_pos hfeedback] at hresult
        exact hresult
      · simp only [hfeedback, Bool.false_eq_true, ↓reduceIte, bind_ok]
        step as ⟨next, hnext⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        have hn : 8 - bit.val = (8 - next.val) + 1 := by scalar_tac
        change crcRounds (8 - next.val) (word.bv >>> 1) = _
        rw [hn, crcRounds, crcBit, if_neg hfeedback] at hresult
        exact hresult
    · have hdone : bit.val = 8 := by scalar_tac
      simpa [hlt, hdone, crcRounds, spec_ok] using hresult
  · exact ⟨hstart, rfl⟩

theorem crc_accumulate_spec (word : U16) (byte : U8) :
    crc_accumulate word byte ⦃ result => result.bv = crcByte word.bv byte ⦄ := by
  unfold crc_accumulate
  simp only [lift, bind_ok]
  step with crc_rounds_spec _ 0#u8 (by decide) as ⟨result, hresult⟩
  change result.bv = crcRounds 8 (word.bv ^^^ byte.bv.zeroExtend 16)
  have heq : (word ^^^ core.convert.num.FromU16U8.from byte).bv =
      word.bv ^^^ byte.bv.zeroExtend 16 := by
    rfl
  simpa only [UScalar.ofNatCore_val_eq, Nat.sub_zero, heq] using hresult

theorem crc_buffer_spec (bytes : Slice U8) (initial : U16) (start : Usize)
    (hstart : start.val ≤ bytes.val.length) :
    crc_mcrf4xx_loop bytes initial start
      ⦃ result => result.bv = (bytes.val.drop start.val).foldl crcByte initial.bv ⦄ := by
  unfold crc_mcrf4xx_loop
  apply loop.spec_decr_nat (fun state => bytes.val.length - state.2.val)
    (fun (word, index) => index.val ≤ bytes.val.length ∧
      (bytes.val.drop index.val).foldl crcByte word.bv =
        (bytes.val.drop start.val).foldl crcByte initial.bv)
  · rintro ⟨word, index⟩ ⟨hindex, hresult⟩
    unfold crc_mcrf4xx_loop.body
    by_cases hlt : index < bytes.len
    · have hlen : index.val < bytes.val.length := by scalar_tac
      simp only [hlt, ↓reduceIte]
      step as ⟨byte, hbyte⟩
      step with crc_accumulate_spec word byte as ⟨nextWord, hword⟩
      step as ⟨nextIndex, hnext⟩
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [List.drop_eq_getElem_cons hlen, List.foldl_cons] at hresult
      simpa only [hnext, hword, hbyte] using hresult
    · have hdone : index.val = bytes.val.length := by scalar_tac
      simpa [hlt, hdone, spec_ok] using hresult
  · exact ⟨hstart, rfl⟩

/-- Total correctness of the extracted CRC loops for every input slice and extra byte. -/
theorem crc_spec (bytes : Slice U8) (extra : U8) :
    crc_mcrf4xx bytes extra ⦃ result => result.bv = crc bytes.val extra ⦄ := by
  unfold crc_mcrf4xx
  step with crc_buffer_spec bytes 65535#u16 0#usize (by simp) as ⟨word, hword⟩
  step with crc_accumulate_spec word extra as ⟨result, hresult⟩
  simpa [crc, hword] using hresult

end RustHammer.Mavlink
