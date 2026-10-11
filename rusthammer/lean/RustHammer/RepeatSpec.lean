import RustHammer.ControlSpec

open RustHammer.Code.grammar.repeat
  RustHammer.Code.input_types

open Aeneas Aeneas.Std

namespace RustHammer.Spec
open Code

/-- The common private bounds invariant. -/
abbrev validRepeatBounds (bounds : RepeatBounds) : Prop :=
  ∀ max, bounds.max = some max → bounds.min.val ≤ max.val

/-- The repetition constructor's private bounds invariant. -/
abbrev validRepeat {P : Type} (parser : Repeat P) : Prop :=
  validRepeatBounds parser.bounds

def repeatNewOutcome {P : Type} (parser : P) (min max : Usize)
    (result : core.result.Result (Repeat P) ConfigError) : Prop :=
  if min.val ≤ max.val then result = .Ok { parser, bounds := { min, max := some max } }
  else result = .Err .InvalidBounds

/-- An attempt's contract may depend on the number of retained items. This makes
first-item versus separator/item behavior explicit even for empty successes. -/
inductive indexedRepetitions {α : Type} (child : Nat → Cursor → Spec.ParseResult α → Prop) :
    Cursor → List α → Cursor → Prop where
  | empty (cursor : Cursor) : indexedRepetitions child cursor [] cursor
  | append {start middle next : Cursor} {values : List α} {value : α}
      (prior : indexedRepetitions child start values middle)
      (last : child values.length middle (.Ok (next, value))) :
      indexedRepetitions child start (values ++ [value]) next

/-- A finite chain of successful child parses. Every invocation contributes one
value, in order, including unit values and successes that consume no input. -/
abbrev repetitions {α : Type} (child : Cursor → ParseResult α → Prop) :
    Cursor → List α → Cursor → Prop :=
  indexedRepetitions (fun _ => child)

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
/-- Bounded repetition returns an ordered chain between its inclusive bounds.
Before the maximum, success requires a recoverably rejected next attempt.
Errors below the minimum and fatal errors propagate.
The specification uses natural counts, independently of the implementation loop
and the allocation strategy of its output vector. -/
abbrev boundedRepetition {α : Type} (child : Cursor → ParseResult α → Prop)
    (min max : Nat) (cursor : Cursor) (outcome : ParseResult (List α)) : Prop :=
  boundedIterations (fun _ => child) min max cursor outcome

/-- Forget only vector storage; the shared repetition contract uses lists. -/
def collectedValues {α : Type} (outcome : Spec.ParseResult (alloc.vec.Vec α)) : Spec.ParseResult (List α) :=
  match outcome with
  | .Ok (next, values) => .Ok (next, values.val)
  | .Err error => .Err error
def boundedRepeat {α : Type} (child : Cursor → Spec.ParseResult α → Prop) (min max : Nat)
    (cursor : Cursor) (outcome : Spec.ParseResult (alloc.vec.Vec α)) : Prop :=
  boundedRepetition child min max cursor (collectedValues outcome)

/-- Successful iterations of an unbounded repetition must move forward to a
normalized position within the input. Other child outcomes are unchanged. -/
def advancing {α : Type} (input : Slice U8) (child : Cursor → Spec.ParseResult α → Prop)
    (cursor : Cursor) (outcome : Spec.ParseResult α) : Prop :=
  child cursor outcome ∧ match outcome with
    | .Ok (next, _) => validCursor input next ∧ position cursor < position next
    | _ => True

/-- The error on a successful child whose position or count cannot be retained.
Cursor validity takes precedence over progress, then the count's representation
limit. Lengths and positions are mathematical naturals, not machine arithmetic. -/
def repeatSuccessError (input : Slice U8) (count : Nat) (before after : Cursor)
    (error : ParseError) : Prop :=
  (¬validCursor input after ∧ error = .InvalidCursor) ∨
  (validCursor input after ∧ position after ≤ position before ∧ error = .NonProgress) ∨
  (validCursor input after ∧ position before < position after ∧
    count = Usize.max ∧ error = .CountOverflow)

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

/-- Unbounded repetition stops on a rejected next attempt, never on an implicit
finite cap. It validates the starting cursor and preserves the full ordered chain
of advancing successes. Progress and representation failures are fatal. -/
abbrev unboundedRepetition {α : Type} (input : Slice U8)
    (child : Cursor → ParseResult α → Prop) (min : Nat) (cursor : Cursor)
    (outcome : ParseResult (List α)) : Prop :=
  unboundedIterations input (fun _ => child) min cursor outcome

def unboundedRepeat {α : Type} (input : Slice U8) (child : Cursor → Spec.ParseResult α → Prop)
    (min : Nat) (cursor : Cursor) (outcome : Spec.ParseResult (alloc.vec.Vec α)) : Prop :=
  unboundedRepetition input child min cursor (collectedValues outcome)

/-- Relate a stored accumulator to the logical sequence of retained child values.
Errors use exactly the same stopping contract as collection. -/
def accumulated {α R : Type} (invariant : List α → R → Prop)
    (repetition : Spec.ParseResult (List α) → Prop) (outcome : Spec.ParseResult R) : Prop :=
  match outcome with
  | .Ok (next, state) => ∃ values, invariant values state ∧ repetition (.Ok (next, values))
  | .Err error => repetition (.Err error)
/-- Exact-count repetition either returns the full chain, or propagates an error
after a strictly shorter successful prefix. Bounds are natural
numbers, and the specification does not depend on a vector's allocation strategy. -/
def repeatN {α : Type} (child : Cursor → Spec.ParseResult α → Prop) (count : Nat)
    (cursor : Cursor) (outcome : Spec.ParseResult (alloc.vec.Vec α)) : Prop :=
  match outcome with
  | .Ok (next, values) => values.val.length = count ∧ repetitions child cursor values.val next
  | .Err error => ∃ (values : List α) (next : Cursor), values.length < count ∧
      repetitions child cursor values next ∧ child next (.Err error)
end RustHammer.Spec
