import RustHammer.RepeatSpec
import RustHammer.PartialProofs

open RustHammer.Code.grammar.repeat
  RustHammer.Code.input_types

open Aeneas Aeneas.Std Result WP

namespace RustHammer.Proofs
open Code

theorem repeat_cursor_valid_spec (input : Slice U8) (cursor : Cursor) :
    repeat_cursor_valid input cursor ⦃ result => result = decide (Spec.validCursor input cursor) ⦄ := by
  by_cases hv : Spec.validCursor input cursor
  · have hparts := hv
    unfold Spec.validCursor Spec.position at hparts
    have hb : cursor.bit < 8#u8 := by scalar_tac
    by_cases hlo : cursor.byte < input.len
    · simp [repeat_cursor_valid, hb, hlo, hv, spec_ok]
    · have heq : cursor.byte = input.len := by scalar_tac
      have hz : cursor.bit = 0#u8 := by scalar_tac
      simp [repeat_cursor_valid, heq, hz, hv, spec_ok]
  · by_cases hb : cursor.bit < 8#u8
    · have hlo : ¬cursor.byte < input.len := by
        intro h
        apply hv
        unfold Spec.validCursor Spec.position
        scalar_tac
      by_cases heq : cursor.byte = input.len
      · have hz : cursor.bit ≠ 0#u8 := by
          intro h
          apply hv
          unfold Spec.validCursor Spec.position
          scalar_tac
        simp [repeat_cursor_valid, hb, heq, hz, hv, spec_ok]
      · simp [repeat_cursor_valid, hb, hlo, heq, hv, spec_ok]
    · simp [repeat_cursor_valid, hb, hv, spec_ok]

theorem repeat_start_spec (input : Slice U8) (cursor : Cursor) (unbounded : Bool) :
    repeat_start input cursor unbounded ⦃ result =>
      result = if unbounded ∧ ¬Spec.validCursor input cursor then .Err .InvalidCursor else .Ok () ⦄ := by
  cases unbounded with
  | false => simp [repeat_start, spec_ok]
  | true =>
    unfold repeat_start
    simp only [↓reduceIte]
    step with repeat_cursor_valid_spec input cursor as ⟨valid, hvalid⟩
    by_cases hv : Spec.validCursor input cursor
    · have htrue : valid = true := by simpa [hv] using hvalid
      simp [htrue, hv, spec_ok]
    · have hfalse : valid = false := by simpa [hv] using hvalid
      simp [hfalse, hv, spec_ok]

theorem repeat_progress_spec (input : Slice U8) (before after : Cursor)
    (hbefore : Spec.validCursor input before) :
    repeat_progress input before after ⦃ result =>
      if Spec.validCursor input after then
        if Spec.position before < Spec.position after then result = .Ok ()
        else result = .Err .NonProgress
      else result = .Err .InvalidCursor ⦄ := by
  unfold repeat_progress
  step with repeat_cursor_valid_spec input after as ⟨valid, hvalid⟩
  by_cases ha : Spec.validCursor input after
  · have htrue : valid = true := by simpa [ha] using hvalid
    have hb := hbefore
    have hab := ha
    unfold Spec.validCursor Spec.position at hb hab
    simp only [htrue, ↓reduceIte, if_pos ha]
    by_cases hlo : after.byte < before.byte
    · have hn : ¬Spec.position before < Spec.position after := by
        unfold Spec.position
        scalar_tac
      simp [hlo, hn, spec_ok]
    · by_cases heq : after.byte = before.byte
      · by_cases hbit : after.bit <= before.bit
        · have hn : ¬Spec.position before < Spec.position after := by
            unfold Spec.position
            scalar_tac
          simp [heq, hbit, hn, spec_ok]
        · have hp : Spec.position before < Spec.position after := by
            unfold Spec.position
            scalar_tac
          simp [heq, hbit, hp, spec_ok]
      · have hp : Spec.position before < Spec.position after := by
          unfold Spec.position
          scalar_tac
        simp [hlo, heq, hp, spec_ok]
  · have hfalse : valid = false := by simpa [ha] using hvalid
    simp [hfalse, ha, spec_ok]

theorem repeat_next_count_success (count : Usize) (hcount : count.val < Usize.max) :
    repeat_next_count count ⦃ result =>
      ∃ next, result = .Ok next ∧ next.val = count.val + 1 ⦄ := by
  have hne : count ≠ core.num.Usize.MAX := by scalar_tac
  simp only [repeat_next_count, hne, ↓reduceIte]
  step as ⟨next, hnext⟩
  exact ⟨next, rfl, hnext⟩

theorem repeat_next_count_overflow (count : Usize) (hcount : count.val = Usize.max) :
    repeat_next_count count ⦃ result => result = .Err .CountOverflow ⦄ := by
  have heq : count = core.num.Usize.MAX := by scalar_tac
  simp [repeat_next_count, heq, spec_ok]

end RustHammer.Proofs
