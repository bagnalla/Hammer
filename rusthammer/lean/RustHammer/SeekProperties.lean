import RustHammer.SeekProofs

open Aeneas Aeneas.Std Result WP
open RustHammer.Code.input_types RustHammer.Code.grammar.position
open RustHammer.Code.parser_traits

namespace RustHammer.Seeking
open Code Proofs

theorem target_success (length : Nat) (cursor next : Cursor) (destination : Int) :
    targetOutcome length cursor destination (.Ok next) ↔
      Spec.validPosition length cursor ∧ Spec.validPosition length next ∧
        (Spec.position next : Int) = destination := by
  unfold targetOutcome
  by_cases hv : Spec.validPosition length cursor
  · rw [if_pos hv]
    by_cases hnegative : destination < 0
    · simp only [if_pos hnegative]
      constructor
      · intro h; cases h
      · rintro ⟨_, _, heq⟩; omega
    · simp only [if_neg hnegative]
      by_cases hout : (8 * length : Nat) < destination
      · simp only [if_pos hout]
        constructor
        · intro h; cases h
        · rintro ⟨_, hn, heq⟩; have := hn.2; omega
      · simp only [if_neg hout, core.result.Result.Ok.injEq]
        constructor
        · rintro ⟨other, rfl, hn, heq⟩; exact ⟨hv, hn, heq⟩
        · rintro ⟨_, hn, heq⟩; exact ⟨next, rfl, hn, heq⟩
  · rw [if_neg hv]
    constructor
    · intro h; cases h
    · rintro ⟨h, _⟩; exact False.elim (hv h)

/-- Successful seeking reports the same cursor it returns. Its position is the
exact mathematical destination, and both entry and destination are valid. -/
theorem success_iff (parser : Seek) (length : Nat) (cursor next value : Cursor)
    (status : InputStatus) :
    outcome parser length cursor status (.Success next value) ↔
      Spec.validPosition length cursor ∧ ¬awaitsEnd parser.target status ∧
        value = next ∧ Spec.validPosition length next ∧
        (Spec.position next : Int) = targetPosition parser.target length cursor := by
  unfold outcome
  by_cases hv : Spec.validPosition length cursor
  · rw [if_pos hv]
    by_cases he : awaitsEnd parser.target status
    · rw [if_pos he]
      constructor
      · intro h; cases h
      · rintro ⟨_, h, _⟩; exact False.elim (h he)
    · rw [if_neg he]
      constructor
      · rintro ⟨raw, hraw, hr⟩
        cases raw with
        | Err error => cases status <;> cases error <;> cases hr
        | Ok destination =>
          have heq : next = destination ∧ value = destination := by
            cases status <;> simpa [Partial.primitiveResult, reported, Spec.completedResult] using hr
          rcases heq with ⟨hnext, hvalue⟩
          subst destination
          have htarget := (target_success length cursor next _).mp hraw
          exact ⟨hv, he, hvalue, htarget.2⟩
      · rintro ⟨_, _, hvalue, hn, hp⟩
        exact ⟨.Ok next, (target_success length cursor next _).mpr ⟨hv, hn, hp⟩,
          by cases status <;> simp [Partial.primitiveResult, reported, Spec.completedResult, hvalue]⟩
  · rw [if_neg hv]
    constructor
    · intro h; cases h
    · rintro ⟨h, _⟩; exact False.elim (hv h)

/-- Absolute and current-relative successes remain successes after extension.
The primitive depends only on length, so even the byte contents are immaterial. -/
theorem success_under_extension (parser : Seek) (length extended : Nat)
    (cursor next : Cursor) (status laterStatus : InputStatus)
    (hfixed : ∀ offset, parser.target ≠ .End offset) (hle : length ≤ extended)
    (h : outcome parser length cursor status (.Success next next)) :
    outcome parser extended cursor laterStatus (.Success next next) := by
  obtain ⟨hv, _, _, hn, hp⟩ := (success_iff parser length cursor next next status).mp h
  have ht : targetPosition parser.target extended cursor = targetPosition parser.target length cursor := by
    cases ht : parser.target with
    | Absolute target => rfl
    | Relative offset => rfl
    | End offset => exact False.elim (hfixed offset ht)
  have he : ¬awaitsEnd parser.target laterStatus := by
    cases ht : parser.target with
    | Absolute target => simp [awaitsEnd]
    | Relative offset => simp [awaitsEnd]
    | End offset => exact False.elim (hfixed offset ht)
  apply (success_iff parser extended cursor next next laterStatus).mpr
  exact ⟨⟨hv.1, by have := hv.2; omega⟩, he, rfl,
    ⟨hn.1, by have := hn.2; omega⟩, by rw [ht]; exact hp⟩

theorem relative_outcome (offset : Isize) (length : Nat) (cursor : Cursor)
    (status : InputStatus) (result : ParseOutcome Cursor) :
    outcome ⟨.Relative offset⟩ length cursor status result ↔
      ∃ raw, targetOutcome length cursor ((Spec.position cursor : Int) + offset.val) raw ∧
        result = Partial.primitiveResult status (reported raw) := by
  by_cases hv : Spec.validPosition length cursor
  · simp only [outcome, if_pos hv, awaitsEnd, if_false, targetPosition]
  · cases status <;> simp [outcome, targetOutcome, hv, reported,
      Partial.primitiveResult, Spec.completedResult]

theorem final_not_more (parser : Seek) (length : Nat) (cursor : Cursor) :
    ¬outcome parser length cursor .Final .NeedMore := by
  have he : ¬awaitsEnd parser.target .Final := by cases parser.target <;> simp [awaitsEnd]
  intro h
  unfold outcome at h
  by_cases hv : Spec.validPosition length cursor
  · rw [if_pos hv, if_neg he] at h
    rcases h with ⟨raw, _, hr⟩
    cases raw <;> cases hr
  · rw [if_neg hv] at h
    cases h

/-- Final execution corresponds to the complete API's ordinary Result, including
invalid-entry errors. This also rules out an incomplete final execution. -/
theorem complete_spec (parser : Seek) (input : Slice U8) (cursor : Cursor) (hp : valid parser) :
    Parser.parse.default (Parser.Blanket (evalInst Direct)) parser input cursor
      ⦃ result => ∃ raw,
        targetOutcome input.val.length cursor (targetPosition parser.target input.val.length cursor) raw ∧
        result = reported raw ⦄ := by
  apply Proofs.complete_spec
  step with with_spec parser input cursor ParseContext.FINAL hp as ⟨result, hresult⟩
  simp only [ParseContext.FINAL] at hresult
  have he : ¬awaitsEnd parser.target .Final := by cases parser.target <;> simp [awaitsEnd]
  unfold outcome at hresult
  by_cases hv : Spec.validPosition input.val.length cursor
  · rw [if_pos hv, if_neg he] at hresult
    rcases hresult with ⟨raw, hraw, rfl⟩
    exact ⟨reported raw, ⟨raw, hraw, rfl⟩, rfl⟩
  · rw [if_neg hv] at hresult
    subst result
    exact ⟨.Err .InvalidCursor, ⟨.Err .InvalidCursor, by simp [targetOutcome, hv], rfl⟩, rfl⟩

end RustHammer.Seeking
