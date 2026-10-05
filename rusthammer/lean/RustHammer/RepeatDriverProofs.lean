import RustHammer.IterationProofs

open Aeneas Aeneas.Std Result WP

namespace RustHammer.Proofs
open Code

/-- Ordinary repetition is the constant-contract specialization of the indexed
attempt sequence. This preserves all existing repetition specifications. -/
theorem indexed_repetitions_constant {α : Type} (child : Cursor → ParseOutcome α → Prop)
    (cursor : Cursor) (values : List α) (next : Cursor) :
    Spec.indexedRepetitions (fun _ => child) cursor values next ↔
      Spec.repetitions child cursor values next := by
  constructor
  · intro h
    induction h with
    | empty => exact Spec.repetitions.empty _
    | append _ last ih => exact Spec.repetitions.append ih last
  · intro h
    induction h with
    | empty => exact Spec.indexedRepetitions.empty _
    | append _ last ih => exact Spec.indexedRepetitions.append ih last

theorem bounded_iterations_constant {α : Type} (child : Cursor → ParseOutcome α → Prop)
    (min max : Nat) (cursor : Cursor) (outcome : ParseOutcome (List α)) :
    Spec.boundedIterations (fun _ => child) min max cursor outcome ↔
      Spec.boundedRepetition child min max cursor outcome := by
  cases outcome <;> simp only [Spec.boundedIterations, Spec.boundedRepetition, indexed_repetitions_constant]

theorem unbounded_iterations_constant {α : Type} (input : Slice U8)
    (child : Cursor → ParseOutcome α → Prop) (min : Nat) (cursor : Cursor)
    (outcome : ParseOutcome (List α)) :
    Spec.unboundedIterations input (fun _ => child) min cursor outcome ↔
      Spec.unboundedRepetition input child min cursor outcome := by
  cases outcome <;> simp only [Spec.unboundedIterations, Spec.unboundedRepetition, indexed_repetitions_constant]

/-- Finite repetition terminates by the remaining permitted calls. The storage
invariant and step contract concern only reachable prefixes and child successes. -/
theorem repeat_run_bounded_spec {P A α R : Type} (pi : Parser P α)
    (ai : RepeatAccumulator A α R) (parser : P) (min max : Usize) (accumulator : A)
    (input : Slice U8) (cursor : Cursor) (context : ParseContext)
    (hbounds : min.val ≤ max.val) (child : Cursor → ParseOutcome α → Prop)
    (invariant : List α → R → Prop)
    (hp : ∀ start, pi.parse_with parser input start context ⦃ result => child start result ⦄)
    (hi : ai.init accumulator ⦃ result => invariant [] result ⦄)
    (hs : ∀ values next after value state,
      Spec.repetitions child cursor values next → child next (.Success after value) →
      values.length < max.val → invariant values state →
      ai.step accumulator state value ⦃ result => invariant (values ++ [value]) result ⦄) :
    repeat_run pi ai parser { min, max := some max } accumulator input cursor context
      ⦃ result => Spec.accumulated invariant
        (Spec.boundedRepetition child min.val max.val cursor) result ⦄ := by
  unfold repeat_run
  step with repeat_run_with_bounded_spec pi pi ai parser parser min max accumulator input cursor context
    hbounds (fun _ => child) invariant
    (by intro count start; unfold repeat_parse; split <;> exact hp start) hi
    (by
      intro values next after value state hprefix hchild hlen hstate
      exact hs values next after value state
        ((indexed_repetitions_constant child cursor values next).mp hprefix) hchild hlen hstate)
    as ⟨outcome, houtcome⟩
  cases outcome <;> simpa only [Spec.accumulated, bounded_iterations_constant] using houtcome

/-- Unbounded repetition terminates by remaining input bits. The accumulator step
runs only after progress and representation checks, including the count limit. -/
theorem repeat_run_unbounded_spec {P A α R : Type} (pi : Parser P α)
    (ai : RepeatAccumulator A α R) (parser : P) (min : Usize) (accumulator : A)
    (input : Slice U8) (cursor : Cursor) (context : ParseContext)
    (child : Cursor → ParseOutcome α → Prop) (invariant : List α → R → Prop)
    (hp : ∀ start, pi.parse_with parser input start context ⦃ result => child start result ⦄)
    (hi : ai.init accumulator ⦃ result => invariant [] result ⦄)
    (hs : ∀ values next after value state,
      Spec.repetitions (Spec.advancing input child) cursor values next →
      Spec.advancing input child next (.Success after value) →
      values.length < Usize.max → invariant values state →
      ai.step accumulator state value ⦃ result => invariant (values ++ [value]) result ⦄) :
    repeat_run pi ai parser { min, max := none } accumulator input cursor context
      ⦃ result => Spec.accumulated invariant
        (Spec.unboundedRepetition input child min.val cursor) result ⦄ := by
  unfold repeat_run
  step with repeat_run_with_unbounded_spec pi pi ai parser parser min accumulator input cursor context
    (fun _ => child) invariant
    (by intro count start; unfold repeat_parse; split <;> exact hp start) hi
    (by
      intro values next after value state hprefix hchild hlen hstate
      exact hs values next after value state
        ((indexed_repetitions_constant (Spec.advancing input child) cursor values next).mp hprefix)
        hchild hlen hstate) as ⟨outcome, houtcome⟩
  cases outcome <;> simpa only [Spec.accumulated, unbounded_iterations_constant] using houtcome

/-- For collection, the stored vector is exactly the logical prefix. -/
theorem accumulated_collection {α : Type} (contract : ParseOutcome (List α) → Prop)
    (outcome : ParseOutcome (alloc.vec.Vec α)) :
    Spec.accumulated (fun values (state : alloc.vec.Vec α) => state.val = values) contract outcome ↔
      contract (Spec.collectedValues outcome) := by
  cases outcome with
  | Success next state => simp [Spec.accumulated, Spec.collectedValues]
  | Error _ => rfl
  | NeedMore => rfl

end RustHammer.Proofs
