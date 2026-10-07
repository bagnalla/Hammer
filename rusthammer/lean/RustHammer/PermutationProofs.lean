import RustHammer.PermutationSpec
import RustHammer.BackendProofs

open Aeneas Aeneas.Std Result WP

namespace RustHammer.Permutation
open Code Proofs

/-- Every search terminates and agrees with the mathematical ordered search when
its entry interpreters terminate. No input-progress or output-cloning assumption
is required. Counter arithmetic is safe for every representable layout size. -/
theorem search_spec {L S B O : Type} (li : permutation.Items L B S O) (items : L)
    (count : Usize) (used : S → Nat → Bool) (clear : S → Nat → S)
    (attempt : AttemptFn S B) (input : Slice U8) (context : ParseContext)
    (hc : li.LayoutInst.count items = ok count)
    (hm : ∀ state index, li.LayoutInst.matched items state index = ok (used state index.val))
    (hl : ∀ state index, li.LayoutInst.clear items state index = ok (clear state index.val))
    (ha : ∀ state index backend cursor,
      li.attempt items state index backend input cursor context
        ⦃ result => result = attempt state index.val backend cursor ⦄)
    (remaining index : Usize) (allAbsent : Bool) (state : S) (backend : B) (cursor : Cursor) :
    permutation.search li items state remaining backend input cursor context index allAbsent
      ⦃ result => result = searchModel count.val used clear attempt remaining.val index.val
        allAbsent state backend cursor ⦄ := by
  induction hr : remaining.val using Nat.strong_induction_on generalizing
      remaining index allAbsent state backend cursor with
  | h r outer =>
    induction hi : count.val - index.val using Nat.strong_induction_on generalizing
        index allAbsent state backend cursor with
    | h todo inner =>
      rw [← hr, permutation.search, searchModel]
      by_cases hz : remaining = 0#usize
      · simp [hz, spec_ok]
      · have hnz : remaining.val ≠ 0 := by scalar_tac
        simp only [hz, hnz, ↓reduceIte, hc, bind_ok]
        by_cases hb : index >= count
        · have hbv : index.val ≥ count.val := by scalar_tac
          simp only [hb, hbv, ↓reduceIte]
          cases allAbsent <;> simp [spec_ok]
        · have hlt : index.val < count.val := by scalar_tac
          have hnb : ¬ index.val ≥ count.val := by omega
          simp only [hb, hnb, ↓reduceIte, hm, bind_ok]
          have later (next : Usize) (hn : next.val = index.val + 1)
              (a : Bool) (s : S) (b : B) :
              permutation.search li items s remaining b input cursor context next a
                ⦃ result => result = searchModel count.val used clear attempt remaining.val
                  (index.val + 1) a s b cursor ⦄ := by
            have hdecr : count.val - next.val < todo := by omega
            simpa only [hn, ← hr] using inner (count.val - next.val) hdecr next a s b cursor rfl
          have hadd : index.val + (1#usize).val ≤ Usize.max := by scalar_tac
          cases hu : used state index.val with
          | true =>
            simp only [↓reduceIte]
            step with Usize.add_spec hadd as ⟨next, hn⟩
            exact later next hn allAbsent state backend
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            step with ha state index backend cursor as ⟨attempted, nextState, nextBackend, hattempt⟩
            rw [← hattempt]
            cases attempted with
            | NeedMore => simp [spec_ok]
            | Absent =>
              step with Usize.add_spec hadd as ⟨next, hn⟩
              exact later next hn allAbsent nextState nextBackend
            | Error error =>
              step with recoverable_spec error as ⟨recover, hrecover⟩
              by_cases he : Spec.recoverable error
              · have ht : recover = true := by simpa [he] using hrecover
                simp only [ht, he, ↓reduceIte]
                step with Usize.add_spec hadd as ⟨next, hn⟩
                exact later next hn false nextState nextBackend
              · have hf : recover = false := by simpa [he] using hrecover
                simp [hf, he, spec_ok]
            | Matched next =>
              step with Usize.sub_spec (x := remaining) (y := 1#usize) (by scalar_tac)
                as ⟨less, hless⟩
              have hdecr : less.val < r := by scalar_tac
              step with outer less.val hdecr less 0#usize true nextState nextBackend next rfl
                as ⟨suffix, finalState, finalBackend, hsuffix⟩
              simp only [hless] at hsuffix
              rw [← hsuffix]
              cases suffix with
              | Success after value => cases value; simp [spec_ok]
              | NeedMore => simp [spec_ok]
              | Error error =>
                step with recoverable_spec error as ⟨recover, hrecover⟩
                by_cases he : Spec.recoverable error
                · have ht : recover = true := by simpa [he] using hrecover
                  simp only [ht, he, ↓reduceIte, hl, bind_ok]
                  step with Usize.add_spec hadd as ⟨following, hn⟩
                  exact later following hn false (clear finalState index.val) finalBackend
                · have hf : recover = false := by simpa [he] using hrecover
                  simp [hf, he, spec_ok]

/-- The public interpreter composes the entry search with typed output assembly.
The backend state from the last attempted child is returned on every outcome. -/
theorem eval_spec {L S B O : Type} (li : permutation.Items L B S O)
    (parser : permutation.Permutation L) (count : Usize)
    (used : S → Nat → Bool) (clear : S → Nat → S) (attempt : AttemptFn S B)
    (empty : S) (finish : S → core.result.Result O ParseError)
    (input : Slice U8) (context : ParseContext)
    (hc : li.LayoutInst.count parser.items = ok count)
    (hm : ∀ state index, li.LayoutInst.matched parser.items state index = ok (used state index.val))
    (hl : ∀ state index, li.LayoutInst.clear parser.items state index = ok (clear state index.val))
    (ha : ∀ state index backend cursor,
      li.attempt parser.items state index backend input cursor context
        ⦃ result => result = attempt state index.val backend cursor ⦄)
    (he : li.LayoutInst.empty parser.items = ok empty)
    (hf : ∀ state, li.LayoutInst.finish parser.items state = ok (finish state))
    (backend : B) (cursor : Cursor) :
    permutation.Permutation.Insts.RusthammerEval.eval li parser backend input cursor context
      ⦃ result => result = finishModel finish
        (searchModel count.val used clear attempt count.val 0 true empty backend cursor) ⦄ := by
  unfold permutation.Permutation.Insts.RusthammerEval.eval
  simp only [he, hc, bind_ok]
  step with search_spec li parser.items count used clear attempt input context hc hm hl ha
    count 0#usize true empty backend cursor as ⟨outcome, state, finalBackend, hsearch⟩
  rw [← hsearch]
  cases outcome with
  | Success next value =>
    cases value
    simp only [hf, bind_ok, finishModel]
    cases finish state <;> simp [spec_ok]
  | Error error => simp [finishModel, spec_ok]
  | NeedMore => simp [finishModel, spec_ok]

theorem required_eq {P : Type} (parser : P) :
    permutation.required parser = ok { parser := parser } := rfl

theorem permutation_eq {T : Type} (items : T) :
    permutation.permutation items = ok { items := items } := rfl

theorem required_eval_spec {P B O : Type} (pi : Eval P B O) (parser : permutation.Required P)
    (backend : B) (input : Slice U8) (cursor : Cursor) (context : ParseContext)
    (post : ParseOutcome O × B → Prop)
    (hp : pi.eval parser.parser backend input cursor context ⦃ result => post result ⦄) :
    permutation.Required.Insts.RusthammerEval.eval pi parser backend input cursor context
      ⦃ result => post result ⦄ := hp

def requiredSlot {O : Type} (outcome : ParseOutcome O) : permutation.Attempt × permutation.Slot O :=
  match outcome with
  | .Success next value => (.Matched next, ⟨true, some value⟩)
  | .Error error => (.Error error, ⟨false, none⟩)
  | .NeedMore => (.NeedMore, ⟨false, none⟩)

def optionalSlot {O : Type} (outcome : ParseOutcome O) : permutation.Attempt × permutation.Slot (Option O) :=
  match outcome with
  | .Success next value => (.Matched next, ⟨true, some (some value)⟩)
  | .Error error => if Spec.recoverable error then (.Absent, ⟨false, some none⟩)
      else (.Error error, ⟨false, none⟩)
  | .NeedMore => (.NeedMore, ⟨false, none⟩)

theorem required_slot_spec {O : Type} (outcome : ParseOutcome O) :
    permutation.required_slot outcome = ok (requiredSlot outcome) := by
  cases outcome <;> simp [permutation.required_slot, requiredSlot, permutation.empty_slot]

theorem optional_slot_spec {O : Type} (outcome : ParseOutcome O) :
    permutation.optional_slot outcome = ok (optionalSlot outcome) := by
  cases outcome with
  | Success next value => rfl
  | NeedMore => simp [permutation.optional_slot, optionalSlot, permutation.empty_slot]
  | Error error =>
    cases error <;> simp [permutation.optional_slot, optionalSlot, Spec.recoverable,
      ParseError.is_recoverable, permutation.empty_slot]

theorem required_entry_spec {P B O : Type} (pi : Eval P B O) (parser : permutation.Required P)
    (backend : B) (input : Slice U8) (cursor : Cursor) (context : ParseContext)
    (child : ParseOutcome O × B → Prop)
    (hp : pi.eval parser.parser backend input cursor context ⦃ result => child result ⦄) :
    permutation.Required.Insts.RusthammerPermutationItemEval.eval_slot pi parser backend input cursor context
      ⦃ result => ∃ outcome final, child (outcome, final) ∧ result = (requiredSlot outcome, final) ⦄ := by
  unfold permutation.Required.Insts.RusthammerPermutationItemEval.eval_slot
  step with hp as ⟨outcome, final, hchild⟩
  simp only [required_slot_spec, bind_ok, spec_ok]
  exact ⟨outcome, final, hchild, rfl⟩

theorem optional_entry_spec {P B O : Type} (pi : Eval P B O) (parser : Optional P)
    (backend : B) (input : Slice U8) (cursor : Cursor) (context : ParseContext)
    (child : ParseOutcome O × B → Prop)
    (hp : pi.eval parser.parser backend input cursor context ⦃ result => child result ⦄) :
    Optional.Insts.RusthammerPermutationItemEvalInputBOption.eval_slot pi parser backend input cursor context
      ⦃ result => ∃ outcome final, child (outcome, final) ∧ result = (optionalSlot outcome, final) ⦄ := by
  unfold Optional.Insts.RusthammerPermutationItemEvalInputBOption.eval_slot
  step with hp as ⟨outcome, final, hchild⟩
  simp only [optional_slot_spec, bind_ok, spec_ok]
  exact ⟨outcome, final, hchild, rfl⟩

theorem empty_eval_spec {B : Type} (backend : B) (input : Slice U8)
    (cursor : Cursor) (context : ParseContext) :
    permutation.Permutation.Insts.RusthammerEval.eval
      (Tuple.Insts.RusthammerPermutationItems0BTupleTuple B) ⟨()⟩ backend input cursor context
      = ok (.Success cursor (), backend) := by
  unfold permutation.Permutation.Insts.RusthammerEval.eval
  simp only [Tuple.Insts.RusthammerPermutationItems0BTupleTuple,
    Tuple.Insts.RusthammerPermutationLayout0TupleTuple,
    Tuple.Insts.RusthammerPermutationLayout0TupleTuple.empty,
    Tuple.Insts.RusthammerPermutationLayout0TupleTuple.count, bind_ok]
  rw [permutation.search]
  simp [Tuple.Insts.RusthammerPermutationLayout0TupleTuple.finish]

end RustHammer.Permutation
