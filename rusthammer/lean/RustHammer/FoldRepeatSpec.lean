import RustHammer.RepeatSpec

open Aeneas Aeneas.Std

namespace RustHammer.Spec
open Code

abbrev validFoldRepeat {P I F : Type} (parser : FoldRepeat P I F) : Prop :=
  validRepeatBounds parser.bounds

def foldRepeatNewOutcome {P I F : Type} (parser : P) (min max : Usize) (init : I) (fold : F)
    (result : core.result.Result (FoldRepeat P I F) ConfigError) : Prop :=
  if min.val ≤ max.val then result = .Ok { parser, bounds := { min, max := some max }, init, fold }
  else result = .Err .InvalidBounds

/-- An initializer followed by one owned-accumulator step for each retained child
value, in order. This mathematical relation needs no cloning, storage, or machine
arithmetic, and permits relational contracts for both callbacks. -/
inductive folds {α R : Type} (initial : R → Prop) (step : R → α → R → Prop) :
    List α → R → Prop where
  | empty {state : R} (init : initial state) : folds initial step [] state
  | append {values : List α} {state next : R} {value : α}
      (prior : folds initial step values state) (last : step state value next) :
      folds initial step (values ++ [value]) next

def boundedFoldRepeat {α R : Type} (child : Cursor → ParseOutcome α → Prop)
    (initial : R → Prop) (step : R → α → R → Prop) (min max : Nat)
    (cursor : Cursor) (outcome : ParseOutcome R) : Prop :=
  accumulated (folds initial step) (boundedRepetition child min max cursor) outcome

def unboundedFoldRepeat {α R : Type} (input : Slice U8) (child : Cursor → ParseOutcome α → Prop)
    (initial : R → Prop) (step : R → α → R → Prop) (min : Nat)
    (cursor : Cursor) (outcome : ParseOutcome R) : Prop :=
  accumulated (folds initial step) (unboundedRepetition input child min cursor) outcome

def boundedFoldRepeatComplete {α R : Type} (child : Cursor → ParseResult α → Prop)
    (initial : R → Prop) (step : R → α → R → Prop) (min max : Nat)
    (cursor : Cursor) (result : ParseResult R) : Prop :=
  boundedFoldRepeat (fun start => completed (child start)) initial step min max cursor (completedResult result)

def unboundedFoldRepeatComplete {α R : Type} (input : Slice U8) (child : Cursor → ParseResult α → Prop)
    (initial : R → Prop) (step : R → α → R → Prop) (min : Nat)
    (cursor : Cursor) (result : ParseResult R) : Prop :=
  unboundedFoldRepeat input (fun start => completed (child start)) initial step min cursor (completedResult result)

end RustHammer.Spec
