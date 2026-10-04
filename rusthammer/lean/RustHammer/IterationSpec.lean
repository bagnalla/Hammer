import RustHammer.RepeatSpec

open Aeneas Aeneas.Std

namespace RustHammer.Spec
open Code

/-- An attempt's contract may depend on the number of retained items. This makes
first-item versus separator/item behavior explicit even for empty successes. -/
inductive indexedRepetitions {α : Type} (child : Nat → Cursor → ParseOutcome α → Prop) :
    Cursor → List α → Cursor → Prop where
  | empty (cursor : Cursor) : indexedRepetitions child cursor [] cursor
  | append {start middle next : Cursor} {values : List α} {value : α}
      (prior : indexedRepetitions child start values middle)
      (last : child values.length middle (.Success next value)) :
      indexedRepetitions child start (values ++ [value]) next

/-- Common finite stopping specification, independent of output storage. -/
def boundedIterations {α : Type} (child : Nat → Cursor → ParseOutcome α → Prop) (min max : Nat)
    (cursor : Cursor) (outcome : ParseOutcome (List α)) : Prop :=
  match outcome with
  | .Success next values => min ≤ values.length ∧ values.length ≤ max ∧
      indexedRepetitions child cursor values next ∧
      (values.length = max ∨ ∃ error, recoverable error ∧ child values.length next (.Error error))
  | .Error error => ∃ (values : List α) (next : Cursor), values.length < max ∧
      indexedRepetitions child cursor values next ∧ child values.length next (.Error error) ∧
      (values.length < min ∨ ¬recoverable error)
  | .NeedMore => ∃ (values : List α) (next : Cursor), values.length < max ∧
      indexedRepetitions child cursor values next ∧ child values.length next .NeedMore

/-- Common unbounded stopping specification. Each whole attempt must advance;
progress and representation failures precede retention or accumulation. -/
def unboundedIterations {α : Type} (input : Slice U8)
    (child : Nat → Cursor → ParseOutcome α → Prop) (min : Nat)
    (cursor : Cursor) (outcome : ParseOutcome (List α)) : Prop :=
  if validCursor input cursor then
    match outcome with
    | .Success next values => min ≤ values.length ∧
        indexedRepetitions (fun n => advancing input (child n)) cursor values next ∧
        ∃ error, recoverable error ∧ child values.length next (.Error error)
    | .Error error => ∃ (values : List α) (next : Cursor), values.length ≤ Usize.max ∧
        indexedRepetitions (fun n => advancing input (child n)) cursor values next ∧
        ((child values.length next (.Error error) ∧ (values.length < min ∨ ¬recoverable error)) ∨
          ∃ after value, child values.length next (.Success after value) ∧
            repeatSuccessError input values.length next after error)
    | .NeedMore => ∃ (values : List α) (next : Cursor), values.length ≤ Usize.max ∧
        indexedRepetitions (fun n => advancing input (child n)) cursor values next ∧
        child values.length next .NeedMore
  else outcome = .Error .InvalidCursor

end RustHammer.Spec
