import RustHammer.ControlProofs

open Aeneas Aeneas.Std Result WP

namespace RustHammer.Backend
open Code Proofs

/-- A child contract records both its parsing result and its state transition.
Input and context are fixed by the surrounding theorem. -/
abbrev Contract (State α : Type) := State → Cursor → ParseOutcome α × State → Prop

def sequence {State α β : Type} (first : Contract State α) (second : Contract State β)
    (state : State) (cursor : Cursor) (result : ParseOutcome (α × β) × State) : Prop :=
  ∃ left middle, first state cursor (left, middle) ∧
    match left with
    | .Success next a => ∃ right final, second middle next (right, final) ∧
        result = (match right with
          | .Success after b => .Success after (a, b)
          | .Error error => .Error error
          | .NeedMore => .NeedMore, final)
    | .Error error => result = (.Error error, middle)
    | .NeedMore => result = (.NeedMore, middle)

/-- Sequencing gives the second child the first child's resulting state and
cursor. Failure and incompleteness retain the last evaluated child's state. -/
theorem seq_eval_spec {State P Q α β : Type} (pi : Eval P State α) (qi : Eval Q State β)
    (parser : Seq P Q) (state : State) (input : Slice U8) (cursor : Cursor) (context : ParseContext)
    (first : Contract State α) (second : Contract State β)
    (hp : pi.eval parser.first state input cursor context ⦃ result => first state cursor result ⦄)
    (hq : ∀ next value middle, first state cursor (.Success next value, middle) →
      qi.eval parser.second middle input next context ⦃ result => second middle next result ⦄) :
    Seq.Insts.RusthammerEvalInputBackendPair.eval pi qi parser state input cursor context
      ⦃ result => sequence first second state cursor result ⦄ := by
  unfold Seq.Insts.RusthammerEvalInputBackendPair.eval
  step with hp as ⟨left, middle, hleft⟩
  cases left with
  | Success next a =>
    step with hq next a middle hleft as ⟨right, final, hright⟩
    cases right <;> simp only [spec_ok]
    all_goals exact ⟨.Success next a, middle, hleft, _, final, hright, rfl⟩
  | Error error =>
    simp only [spec_ok]
    exact ⟨.Error error, middle, hleft, rfl⟩
  | NeedMore =>
    simp only [spec_ok]
    exact ⟨.NeedMore, middle, hleft, rfl⟩

def choice {State α : Type} (first second : Contract State α)
    (state : State) (cursor : Cursor) (result : ParseOutcome α × State) : Prop :=
  ∃ left middle, first state cursor (left, middle) ∧
    match left with
    | .Error error => if Spec.recoverable error then second middle cursor result
        else result = (left, middle)
    | _ => result = (left, middle)

/-- An alternative restores the original cursor but retains state from the
rejected first child. Fatal errors and incompleteness do not try the alternative. -/
theorem choice_eval_spec {State P Q α : Type} (pi : Eval P State α) (qi : Eval Q State α)
    (parser : Choice P Q) (state : State) (input : Slice U8) (cursor : Cursor) (context : ParseContext)
    (first second : Contract State α)
    (hp : pi.eval parser.first state input cursor context ⦃ result => first state cursor result ⦄)
    (hq : ∀ error middle, first state cursor (.Error error, middle) → Spec.recoverable error →
      qi.eval parser.second middle input cursor context ⦃ result => second middle cursor result ⦄) :
    Choice.Insts.RusthammerEval.eval pi qi parser state input cursor context
      ⦃ result => choice first second state cursor result ⦄ := by
  unfold Choice.Insts.RusthammerEval.eval
  step with hp as ⟨left, middle, hleft⟩
  cases left with
  | Success next value =>
    simp only [spec_ok]
    exact ⟨.Success next value, middle, hleft, rfl⟩
  | NeedMore =>
    simp only [spec_ok]
    exact ⟨.NeedMore, middle, hleft, rfl⟩
  | Error error =>
    step with recoverable_spec error as ⟨recover, hrecover⟩
    by_cases h : Spec.recoverable error
    · have heq : recover = true := by simpa [h] using hrecover
      simp only [heq, ↓reduceIte]
      step with hq error middle hleft h as ⟨result, hresult⟩
      exact ⟨.Error error, middle, hleft, by simpa [h] using hresult⟩
    · have heq : recover = false := by simpa [h] using hrecover
      simp only [heq, Bool.false_eq_true, ↓reduceIte, spec_ok]
      exact ⟨.Error error, middle, hleft, by simp [h]⟩

end RustHammer.Backend
