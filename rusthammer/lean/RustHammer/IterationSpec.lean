import RustHammer.RepeatSpec

open RustHammer.Code.input_types

open Aeneas Aeneas.Std

namespace RustHammer.Spec
open Code

/-- An attempt's contract may depend on the number of retained items. This makes
first-item versus separator/item behavior explicit even for empty successes. -/
inductive indexedRepetitions {α : Type} (child : Nat → Cursor → Spec.ParseResult α → Prop) :
    Cursor → List α → Cursor → Prop where
  | empty (cursor : Cursor) : indexedRepetitions child cursor [] cursor
  | append {start middle next : Cursor} {values : List α} {value : α}
      (prior : indexedRepetitions child start values middle)
      (last : child values.length middle (.Ok (next, value))) :
      indexedRepetitions child start (values ++ [value]) next

/-- Common finite stopping specification, independent of output storage. -/
def boundedIterations {α : Type} (child : Nat → Cursor → Spec.ParseResult α → Prop) (min max : Nat)
    (cursor : Cursor) (outcome : Spec.ParseResult (List α)) : Prop :=
  match outcome with
  | .Ok (next, values) => min ≤ values.length ∧ values.length ≤ max ∧
      indexedRepetitions child cursor values next ∧
      (values.length = max ∨ ∃ error, recoverable error ∧ child values.length next (.Err error))
  | .Err error => ∃ (values : List α) (next : Cursor), values.length < max ∧
      indexedRepetitions child cursor values next ∧ child values.length next (.Err error) ∧
      (values.length < min ∨ ¬recoverable error)
/-- Common unbounded stopping specification. Each whole attempt must advance;
progress and representation failures precede retention or accumulation. -/
def unboundedIterations {α : Type} (input : Slice U8)
    (child : Nat → Cursor → Spec.ParseResult α → Prop) (min : Nat)
    (cursor : Cursor) (outcome : Spec.ParseResult (List α)) : Prop :=
  if validCursor input cursor then
    match outcome with
    | .Ok (next, values) => min ≤ values.length ∧
        indexedRepetitions (fun n => advancing input (child n)) cursor values next ∧
        ∃ error, recoverable error ∧ child values.length next (.Err error)
    | .Err error => ∃ (values : List α) (next : Cursor), values.length ≤ Usize.max ∧
        indexedRepetitions (fun n => advancing input (child n)) cursor values next ∧
        ((child values.length next (.Err error) ∧ (values.length < min ∨ ¬recoverable error)) ∨
          ∃ after value, child values.length next (.Ok (after, value)) ∧
            repeatSuccessError input values.length next after error)
  else outcome = .Err .InvalidCursor

end RustHammer.Spec
