import RustHammer.RepeatSupport
import RustHammer.IterationSpec

open Aeneas Aeneas.Std Result WP

namespace RustHammer.Proofs
open Code

/-- Finite repetition terminates by the remaining permitted calls. The storage
invariant and step contract concern only reachable prefixes and child successes. -/
theorem repeat_run_with_bounded_spec {P Q A α R : Type} (pi : Parser P α) (qi : Parser Q α)
    (ai : RepeatAccumulator A α R) (parser : P) (following : Q) (min max : Usize) (accumulator : A)
    (input : Slice U8) (cursor : Cursor) (context : ParseContext)
    (hbounds : min.val ≤ max.val) (child : Nat → Cursor → ParseOutcome α → Prop)
    (invariant : List α → R → Prop)
    (hp : ∀ count start, repeat_parse pi qi parser following count input start context
      ⦃ result => child count.val start result ⦄)
    (hi : ai.init accumulator ⦃ result => invariant [] result ⦄)
    (hs : ∀ values next after value state,
      Spec.indexedRepetitions child cursor values next → child values.length next (.Success after value) →
      values.length < max.val → invariant values state →
      ai.step accumulator state value ⦃ result => invariant (values ++ [value]) result ⦄) :
    repeat_run_with pi qi ai parser following { min, max := some max } accumulator input cursor context
      ⦃ result => Spec.accumulated invariant
        (Spec.boundedIterations child min.val max.val cursor) result ⦄ := by
  unfold repeat_run_with
  simp only [core.option.Option.is_none, Option.isNone, repeat_start, Bool.false_eq_true,
    ↓reduceIte, bind_ok]
  step with hi as ⟨initial, hinitial⟩
  unfold repeat_run_with_loop
  apply loop.spec_decr_nat (fun state => max.val - state.2.2.val)
    (fun (state, next, count) => ∃ values : List α, values.length = count.val ∧
      count.val ≤ max.val ∧ Spec.indexedRepetitions child cursor values next ∧ invariant values state)
  · rintro ⟨state, next, count⟩ ⟨values, hcount, hbound, hprefix, hinvariant⟩
    unfold repeat_run_with_loop.body
    simp only [repeat_below_max, bind_ok, decide_eq_true_eq]
    by_cases hmore : count < max
    · have hless : count.val < max.val := by scalar_tac
      simp only [hmore, ↓reduceIte]
      step with hp count next as ⟨parsed, hparsed⟩
      rw [← hcount] at hparsed
      cases parsed with
      | Success after value =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        step with repeat_next_count_success count (by scalar_tac) as ⟨incremented, following, heq, hfollowing⟩
        simp only [heq]
        step with hs values next after value state hprefix hparsed (by omega) hinvariant
          as ⟨appended, happended⟩
        refine ⟨⟨values ++ [value], ?_, ?_, Spec.indexedRepetitions.append hprefix hparsed, happended⟩, ?_⟩
        · simp only [List.length_append, List.length_singleton]; omega
        · omega
        · omega
      | Error error =>
        by_cases hmin : count >= min
        · have hminimum : min.val ≤ count.val := by scalar_tac
          simp only [hmin, ↓reduceIte]
          step with recoverable_spec error as ⟨recover, hrecover⟩
          by_cases hreject : Spec.recoverable error
          · have htrue : recover = true := by simpa [hreject] using hrecover
            simp only [htrue, ↓reduceIte, spec_ok]
            exact ⟨values, hinvariant, by omega, by omega, hprefix, Or.inr ⟨error, hreject, hparsed⟩⟩
          · have hfalse : recover = false := by simpa [hreject] using hrecover
            simp only [hfalse, Bool.false_eq_true, ↓reduceIte, spec_ok]
            exact ⟨values, next, by omega, hprefix, hparsed, Or.inr hreject⟩
        · have hbelow : count.val < min.val := by scalar_tac
          simp only [hmin, ↓reduceIte, spec_ok]
          exact ⟨values, next, by omega, hprefix, hparsed, Or.inl (by omega)⟩
      | NeedMore => exact ⟨values, next, by omega, hprefix, hparsed⟩
    · have heq : count.val = max.val := by scalar_tac
      simp only [hmore, ↓reduceIte, spec_ok]
      exact ⟨values, hinvariant, by omega, by omega, hprefix, Or.inl (by omega)⟩
  · exact ⟨[], by simp, by scalar_tac, Spec.indexedRepetitions.empty cursor, hinitial⟩

/-- Unbounded repetition terminates by remaining input bits. The accumulator step
runs only after progress and representation checks, including the count limit. -/
theorem repeat_run_with_unbounded_spec {P Q A α R : Type} (pi : Parser P α) (qi : Parser Q α)
    (ai : RepeatAccumulator A α R) (parser : P) (following : Q) (min : Usize) (accumulator : A)
    (input : Slice U8) (cursor : Cursor) (context : ParseContext)
    (child : Nat → Cursor → ParseOutcome α → Prop) (invariant : List α → R → Prop)
    (hp : ∀ count start, repeat_parse pi qi parser following count input start context
      ⦃ result => child count.val start result ⦄)
    (hi : ai.init accumulator ⦃ result => invariant [] result ⦄)
    (hs : ∀ values next after value state,
      Spec.indexedRepetitions (fun n => Spec.advancing input (child n)) cursor values next →
      Spec.advancing input (child values.length) next (.Success after value) →
      values.length < Usize.max → invariant values state →
      ai.step accumulator state value ⦃ result => invariant (values ++ [value]) result ⦄) :
    repeat_run_with pi qi ai parser following { min, max := none } accumulator input cursor context
      ⦃ result => Spec.accumulated invariant
        (Spec.unboundedIterations input child min.val cursor) result ⦄ := by
  unfold repeat_run_with
  simp only [core.option.Option.is_none, Option.isNone]
  step with repeat_start_spec input cursor true as ⟨initial, hinitial⟩
  by_cases hvalid : Spec.validCursor input cursor
  · have hiok : initial = .Ok () := by simpa [hvalid] using hinitial
    simp only [hiok]
    step with hi as ⟨initialState, hinit⟩
    unfold repeat_run_with_loop
    apply loop.spec_decr_nat (fun state => 8 * input.val.length - Spec.position state.2.1)
      (fun (state, next, count) => ∃ values : List α, values.length = count.val ∧
        Spec.validCursor input next ∧
        Spec.indexedRepetitions (fun n => Spec.advancing input (child n)) cursor values next ∧ invariant values state)
    · rintro ⟨state, next, count⟩ ⟨values, hcount, hnext, hprefix, hinvariant⟩
      unfold repeat_run_with_loop.body
      simp only [repeat_below_max, bind_ok, ↓reduceIte]
      step with hp count next as ⟨parsed, hparsed⟩
      rw [← hcount] at hparsed
      cases parsed with
      | Success after value =>
        step with repeat_progress_spec input next after hnext as ⟨progress, hprogress⟩
        by_cases hafter : Spec.validCursor input after
        · by_cases hforward : Spec.position next < Spec.position after
          · simp only [if_pos hafter, if_pos hforward] at hprogress
            simp only [hprogress]
            by_cases hroom : count.val < Usize.max
            · step with repeat_next_count_success count hroom as ⟨incremented, following, heq, hfollowing⟩
              simp only [heq]
              step with hs values next after value state hprefix ⟨hparsed, hafter, hforward⟩
                (by omega) hinvariant as ⟨appended, happended⟩
              refine ⟨⟨values ++ [value], ?_, hafter.1, hafter.2,
                Spec.indexedRepetitions.append hprefix ⟨hparsed, hafter, hforward⟩, happended⟩, ?_⟩
              · simp only [List.length_append, List.length_singleton]; omega
              · have hbound := hafter.2; omega
            · have hfull : count.val = Usize.max := by scalar_tac
              step with repeat_next_count_overflow count hfull as ⟨overflow, hoverflow⟩
              simp only [hoverflow, spec_ok, Spec.accumulated, Spec.unboundedIterations, if_pos hvalid]
              exact ⟨values, next, by scalar_tac, hprefix, Or.inr ⟨after, value, hparsed,
                Or.inr (Or.inr ⟨hafter, hforward, by omega, rfl⟩)⟩⟩
          · simp only [if_pos hafter, if_neg hforward] at hprogress
            simp only [hprogress, spec_ok, Spec.accumulated, Spec.unboundedIterations, if_pos hvalid]
            exact ⟨values, next, by scalar_tac, hprefix, Or.inr ⟨after, value, hparsed,
              Or.inr (Or.inl ⟨hafter, by omega, rfl⟩)⟩⟩
        · simp only [if_neg hafter] at hprogress
          simp only [hprogress, spec_ok, Spec.accumulated, Spec.unboundedIterations, if_pos hvalid]
          exact ⟨values, next, by scalar_tac, hprefix,
            Or.inr ⟨after, value, hparsed, Or.inl ⟨hafter, rfl⟩⟩⟩
      | Error error =>
        by_cases hmin : count >= min
        · have hminimum : min.val ≤ count.val := by scalar_tac
          simp only [hmin, ↓reduceIte]
          step with recoverable_spec error as ⟨recover, hrecover⟩
          by_cases hreject : Spec.recoverable error
          · have htrue : recover = true := by simpa [hreject] using hrecover
            simp only [htrue, ↓reduceIte, spec_ok, Spec.accumulated]
            refine ⟨values, hinvariant, ?_⟩
            simp only [Spec.unboundedIterations, if_pos hvalid]
            exact ⟨by omega, hprefix, error, hreject, hparsed⟩
          · have hfalse : recover = false := by simpa [hreject] using hrecover
            simp only [hfalse, Bool.false_eq_true, ↓reduceIte, spec_ok,
              Spec.accumulated, Spec.unboundedIterations, if_pos hvalid]
            exact ⟨values, next, by scalar_tac, hprefix, Or.inl ⟨hparsed, Or.inr hreject⟩⟩
        · have hbelow : count.val < min.val := by scalar_tac
          simp only [hmin, ↓reduceIte, spec_ok, Spec.accumulated,
            Spec.unboundedIterations, if_pos hvalid]
          exact ⟨values, next, by scalar_tac, hprefix, Or.inl ⟨hparsed, Or.inl (by omega)⟩⟩
      | NeedMore =>
        simp only [spec_ok, Spec.accumulated, Spec.unboundedIterations, if_pos hvalid]
        exact ⟨values, next, by scalar_tac, hprefix, hparsed⟩
    · exact ⟨[], by simp, hvalid, Spec.indexedRepetitions.empty cursor, hinit⟩
  · simp [hvalid] at hinitial
    simp [hinitial, Spec.accumulated, Spec.unboundedIterations, hvalid, spec_ok]

end RustHammer.Proofs
