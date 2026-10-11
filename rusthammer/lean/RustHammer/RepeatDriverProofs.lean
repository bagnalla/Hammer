import RustHammer.IterationProofs

open RustHammer.Code.grammar.repeat
  RustHammer.Code.input_types

open Aeneas Aeneas.Std Result WP

namespace RustHammer.Proofs
open Code

/-- Finite repetition terminates by the remaining permitted calls. The storage
invariant and step contract concern only reachable prefixes and child successes. -/
theorem repeat_run_bounded_spec {P A α R : Type} (pi : parser_traits.Parser P α)
    (ai : RepeatAccumulator A α R) (parser : P) (min max : Usize) (accumulator : A)
    (input : Slice U8) (cursor : Cursor) (context : ByteOrder)
    (hbounds : min.val ≤ max.val) (child : Cursor → Spec.ParseResult α → Prop)
    (invariant : List α → R → Prop)
    (hp : ∀ start, pi.parse_with parser input start context ⦃ result => child start result ⦄)
    (hi : ai.init accumulator ⦃ result => invariant [] result ⦄)
    (hs : ∀ values next after value state,
      Spec.repetitions child cursor values next → child next (.Ok (after, value)) →
      values.length < max.val → invariant values state →
      ai.step accumulator state value ⦃ result => invariant (values ++ [value]) result ⦄) :
    grammar.repeat.repeat_run pi ai parser { min, max := some max } accumulator input cursor context
      ⦃ result => Spec.accumulated invariant
        (Spec.boundedRepetition child min.val max.val cursor) result ⦄ := by
  rw [grammar.repeat.repeat_run]
  exact repeat_run_with_bounded_spec pi pi ai parser parser min max accumulator input cursor context
    hbounds (fun _ => child) invariant
    (by intro count start; rw [grammar.repeat.repeat_parse]; split <;> exact hp start) hi hs

/-- Unbounded repetition terminates by remaining input bits. The accumulator step
runs only after progress and representation checks, including the count limit. -/
theorem repeat_run_unbounded_spec {P A α R : Type} (pi : parser_traits.Parser P α)
    (ai : RepeatAccumulator A α R) (parser : P) (min : Usize) (accumulator : A)
    (input : Slice U8) (cursor : Cursor) (context : ByteOrder)
    (child : Cursor → Spec.ParseResult α → Prop) (invariant : List α → R → Prop)
    (hp : ∀ start, pi.parse_with parser input start context ⦃ result => child start result ⦄)
    (hi : ai.init accumulator ⦃ result => invariant [] result ⦄)
    (hs : ∀ values next after value state,
      Spec.repetitions (Spec.advancing input child) cursor values next →
      Spec.advancing input child next (.Ok (after, value)) →
      values.length < Usize.max → invariant values state →
      ai.step accumulator state value ⦃ result => invariant (values ++ [value]) result ⦄) :
    grammar.repeat.repeat_run pi ai parser { min, max := none } accumulator input cursor context
      ⦃ result => Spec.accumulated invariant
        (Spec.unboundedRepetition input child min.val cursor) result ⦄ := by
  rw [grammar.repeat.repeat_run]
  exact repeat_run_with_unbounded_spec pi pi ai parser parser min accumulator input cursor context
    (fun _ => child) invariant
    (by intro count start; rw [grammar.repeat.repeat_parse]; split <;> exact hp start) hi hs

/-- For collection, the stored vector is exactly the logical prefix. -/
theorem accumulated_collection {α : Type} (contract : Spec.ParseResult (List α) → Prop)
    (outcome : Spec.ParseResult (alloc.vec.Vec α)) :
    Spec.accumulated (fun values (state : alloc.vec.Vec α) => state.val = values) contract outcome ↔
      contract (Spec.collectedValues outcome) := by
  cases outcome with
  | Ok pair =>
    rcases pair with ⟨next, state⟩
    simp [Spec.accumulated, Spec.collectedValues]
  | Err _ => rfl
end RustHammer.Proofs
