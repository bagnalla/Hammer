import RustHammer.SeekSpec
import RustHammer.PositionProofs

open Aeneas Aeneas.Std Result WP
open RustHammer.Code.input_types RustHammer.Code.grammar.position
open RustHammer.Code.parser_traits

namespace RustHammer.Seeking
open Code Proofs

/-- Every operation in the subtraction helper is safe for every machine length,
raw cursor, and unsigned count, including counts larger than any signed offset. -/
theorem retreat_cursor_spec (length : Usize) (cursor : Cursor) (bits : Usize) :
    retreat_cursor length cursor bits
      ⦃ result => retreatOutcome length.val cursor bits.val result ⦄ := by
  unfold retreat_cursor
  step with advance_cursor_zero_spec length cursor as ⟨checked, hchecked⟩
  by_cases hv : Spec.validPosition length.val cursor
  · simp only [if_pos hv] at hchecked
    simp only [hchecked, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    have hparts := hv
    unfold Spec.validPosition Spec.position at hparts
    step as ⟨whole, hwhole⟩
    step as ⟨remainder, hremainder⟩
    step with UScalar.cast_inBounds_spec .U8 remainder (by scalar_tac) as ⟨tail, htail⟩
    by_cases hborrow : tail > cursor.bit
    · simp only [if_pos hborrow]
      step as ⟨bytes, hbytes⟩
      step as ⟨sum, hsum⟩
      step as ⟨bit, hbit⟩
      by_cases hshort : bytes > cursor.byte
      · have hn : ¬bits.val ≤ Spec.position cursor := by
          unfold Spec.position; scalar_tac
        simpa [hshort, retreatOutcome, hn, spec_ok] using hv
      · simp only [if_neg hshort]
        step as ⟨byte, hbyte⟩
        have hfit : bits.val ≤ Spec.position cursor := by
          unfold Spec.position; scalar_tac
        simp only [retreatOutcome, if_pos hv, if_pos hfit]
        refine ⟨⟨byte, bit⟩, rfl, ?_, ?_⟩
        · unfold Spec.validPosition Spec.position; scalar_tac
        · unfold Spec.position; scalar_tac
    · simp only [if_neg hborrow]
      step as ⟨bit, hbit⟩
      by_cases hshort : whole > cursor.byte
      · have hn : ¬bits.val ≤ Spec.position cursor := by
          unfold Spec.position; scalar_tac
        simpa [hshort, retreatOutcome, hn, spec_ok] using hv
      · simp only [if_neg hshort]
        step as ⟨byte, hbyte⟩
        have hfit : bits.val ≤ Spec.position cursor := by
          unfold Spec.position; scalar_tac
        simp only [retreatOutcome, if_pos hv, if_pos hfit]
        refine ⟨⟨byte, bit⟩, rfl, ?_, ?_⟩
        · unfold Spec.validPosition Spec.position; scalar_tac
        · unfold Spec.position; scalar_tac
  · simp only [if_neg hv] at hchecked
    simp [hchecked, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      retreatOutcome, hv, spec_ok]

private theorem retreat_target (length : Nat) (cursor : Cursor) (bits : Nat)
    (result : core.result.Result Cursor ParseError)
    (h : retreatOutcome length cursor bits result) :
    targetOutcome length cursor ((Spec.position cursor : Int) - bits) result := by
  unfold retreatOutcome at h
  unfold targetOutcome
  split at h
  next hv =>
    simp only [if_pos hv]
    split at h
    next hfit =>
      have hnonneg : ¬(Spec.position cursor : Int) - bits < 0 := by omega
      have hin : ¬(8 * length : Nat) < (Spec.position cursor : Int) - bits := by
        have := hv.2; omega
      simp only [if_neg hnonneg, if_neg hin]
      rcases h with ⟨next, rfl, hn, hp⟩
      exact ⟨next, rfl, hn, by omega⟩
    next hshort =>
      have hnegative : (Spec.position cursor : Int) - bits < 0 := by omega
      simpa only [if_pos hnegative] using h
  next hv => simpa only [if_neg hv] using h

private theorem advance_target (length : Nat) (cursor : Cursor) (bits : Nat)
    (result : core.result.Result Cursor ParseError)
    (h : Spec.advanceOutcome length cursor bits result) :
    targetOutcome length cursor ((Spec.position cursor : Int) + bits) result := by
  unfold Spec.advanceOutcome at h
  unfold targetOutcome
  split at h
  next hv =>
    have hnonneg : ¬(Spec.position cursor : Int) + bits < 0 := by omega
    simp only [if_pos hv, if_neg hnonneg]
    split at h
    next hfit =>
      have hin : ¬(8 * length : Nat) < (Spec.position cursor : Int) + bits := by omega
      simp only [if_neg hin]
      rcases h with ⟨next, rfl, hn, hp⟩
      exact ⟨next, rfl, hn, by omega⟩
    next hshort =>
      have hout : (8 * length : Nat) < (Spec.position cursor : Int) + bits := by omega
      simpa only [if_pos hout] using h
  next hv => simpa only [if_neg hv] using h

/-- Signed movement is total even for the minimum signed offset. Absolute bit
positions are mathematical integers and need not fit in a machine word. -/
theorem offset_cursor_spec (length : Usize) (cursor : Cursor) (offset : Isize) :
    offset_cursor length cursor offset
      ⦃ result => targetOutcome length.val cursor
        ((Spec.position cursor : Int) + offset.val) result ⦄ := by
  have hbounds : IScalar.min .Isize < 0 ∧ 0 ≤ IScalar.max .Isize ∧
      IScalar.max .Isize < (UScalar.max .Usize : Int) ∧
      -IScalar.min .Isize ≤ (UScalar.max .Usize : Int) := by
    rcases System.Platform.numBits_eq with h | h <;>
      simp [IScalar.min, IScalar.max, UScalar.max, h]
  unfold offset_cursor
  split
  next hnegative =>
    step with IScalar.add_spec (x := offset) (y := 1#isize) (by scalar_tac) (by scalar_tac) as ⟨almost, halmost⟩
    step with HNeg.hNeg.step almost (by scalar_tac) as ⟨positive, hpositive⟩
    step with IScalar.hcast_inBounds_spec .Usize positive (by scalar_tac) as ⟨unsigned, hunsigned⟩
    step with UScalar.add_spec (x := unsigned) (y := 1#usize) (by scalar_tac) as ⟨magnitude, hmagnitude⟩
    step with retreat_cursor_spec length cursor magnitude as ⟨result, hresult⟩
    have hm : (magnitude.val : Int) = -offset.val := by scalar_tac
    simpa only [hm, sub_neg_eq_add] using retreat_target length.val cursor magnitude.val result hresult
  next hnonnegative =>
    step with IScalar.hcast_inBounds_spec .Usize offset (by scalar_tac) as ⟨magnitude, hmagnitude⟩
    step with advance_cursor_spec length cursor magnitude as ⟨result, hresult⟩
    simpa only [hmagnitude] using advance_target length.val cursor magnitude.val result hresult

end RustHammer.Seeking
