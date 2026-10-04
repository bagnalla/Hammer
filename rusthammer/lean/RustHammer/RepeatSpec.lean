import RustHammer.PartialSpec

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

/-- A finite chain of successful child parses. Every invocation contributes one
value, in order, including unit values and successes that consume no input. -/
inductive repetitions {α : Type} (child : Cursor → ParseOutcome α → Prop) :
    Cursor → List α → Cursor → Prop where
  | empty (cursor : Cursor) : repetitions child cursor [] cursor
  | append {start middle next : Cursor} {values : List α} {value : α}
      (hprefix : repetitions child start values middle)
      (last : child middle (.Success next value)) :
      repetitions child start (values ++ [value]) next

/-- Bounded repetition returns an ordered chain between its inclusive bounds.
Before the maximum, success requires a recoverably rejected next attempt.
Errors below the minimum and fatal errors propagate; incompleteness always does.
The specification uses natural counts, independently of the implementation loop
and the allocation strategy of its output vector. -/
def boundedRepetition {α : Type} (child : Cursor → ParseOutcome α → Prop) (min max : Nat)
    (cursor : Cursor) (outcome : ParseOutcome (List α)) : Prop :=
  match outcome with
  | .Success next values => min ≤ values.length ∧ values.length ≤ max ∧
      repetitions child cursor values next ∧
      (values.length = max ∨ ∃ error, recoverable error ∧ child next (.Error error))
  | .Error error => ∃ (values : List α) (next : Cursor), values.length < max ∧
      repetitions child cursor values next ∧ child next (.Error error) ∧
      (values.length < min ∨ ¬recoverable error)
  | .NeedMore => ∃ (values : List α) (next : Cursor), values.length < max ∧
      repetitions child cursor values next ∧ child next .NeedMore

/-- Forget only vector storage; the shared repetition contract uses lists. -/
def collectedValues {α : Type} (outcome : ParseOutcome (alloc.vec.Vec α)) : ParseOutcome (List α) :=
  match outcome with
  | .Success next values => .Success next values.val
  | .Error error => .Error error
  | .NeedMore => .NeedMore

def boundedRepeat {α : Type} (child : Cursor → ParseOutcome α → Prop) (min max : Nat)
    (cursor : Cursor) (outcome : ParseOutcome (alloc.vec.Vec α)) : Prop :=
  boundedRepetition child min max cursor (collectedValues outcome)

def boundedRepeatComplete {α : Type} (child : Cursor → ParseResult α → Prop) (min max : Nat)
    (cursor : Cursor) (result : ParseResult (alloc.vec.Vec α)) : Prop :=
  boundedRepeat (fun start => completed (child start)) min max cursor (completedResult result)

/-- Successful iterations of an unbounded repetition must move forward to a
normalized position within the input. Other child outcomes are unchanged. -/
def advancing {α : Type} (input : Slice U8) (child : Cursor → ParseOutcome α → Prop)
    (cursor : Cursor) (outcome : ParseOutcome α) : Prop :=
  child cursor outcome ∧ match outcome with
    | .Success next _ => validCursor input next ∧ position cursor < position next
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

/-- Unbounded repetition stops on a rejected next attempt, never on an implicit
finite cap. It validates the starting cursor and preserves the full ordered chain
of advancing successes. Progress and representation failures are fatal. -/
def unboundedRepetition {α : Type} (input : Slice U8) (child : Cursor → ParseOutcome α → Prop)
    (min : Nat) (cursor : Cursor) (outcome : ParseOutcome (List α)) : Prop :=
  if validCursor input cursor then
    match outcome with
    | .Success next values => min ≤ values.length ∧
        repetitions (advancing input child) cursor values next ∧
        ∃ error, recoverable error ∧ child next (.Error error)
    | .Error error => ∃ (values : List α) (next : Cursor),
        values.length ≤ Usize.max ∧
        repetitions (advancing input child) cursor values next ∧
        ((child next (.Error error) ∧ (values.length < min ∨ ¬recoverable error)) ∨
          ∃ after value, child next (.Success after value) ∧
            repeatSuccessError input values.length next after error)
    | .NeedMore => ∃ (values : List α) (next : Cursor),
        values.length ≤ Usize.max ∧
        repetitions (advancing input child) cursor values next ∧ child next .NeedMore
  else outcome = .Error .InvalidCursor

def unboundedRepeat {α : Type} (input : Slice U8) (child : Cursor → ParseOutcome α → Prop)
    (min : Nat) (cursor : Cursor) (outcome : ParseOutcome (alloc.vec.Vec α)) : Prop :=
  unboundedRepetition input child min cursor (collectedValues outcome)

/-- Relate a stored accumulator to the logical sequence of retained child values.
Errors and incompleteness use exactly the same stopping contract as collection. -/
def accumulated {α R : Type} (invariant : List α → R → Prop)
    (repetition : ParseOutcome (List α) → Prop) (outcome : ParseOutcome R) : Prop :=
  match outcome with
  | .Success next state => ∃ values, invariant values state ∧ repetition (.Success next values)
  | .Error error => repetition (.Error error)
  | .NeedMore => repetition .NeedMore

def unboundedRepeatComplete {α : Type} (input : Slice U8)
    (child : Cursor → ParseResult α → Prop) (min : Nat)
    (cursor : Cursor) (result : ParseResult (alloc.vec.Vec α)) : Prop :=
  unboundedRepeat input (fun start => completed (child start)) min cursor (completedResult result)

/-- Exact-count repetition either returns the full chain, or propagates an error
or incompleteness after a strictly shorter successful prefix. Bounds are natural
numbers, and the specification does not depend on a vector's allocation strategy. -/
def repeatN {α : Type} (child : Cursor → ParseOutcome α → Prop) (count : Nat)
    (cursor : Cursor) (outcome : ParseOutcome (alloc.vec.Vec α)) : Prop :=
  match outcome with
  | .Success next values => values.val.length = count ∧ repetitions child cursor values.val next
  | .Error error => ∃ (values : List α) (next : Cursor), values.length < count ∧
      repetitions child cursor values next ∧ child next (.Error error)
  | .NeedMore => ∃ (values : List α) (next : Cursor), values.length < count ∧
      repetitions child cursor values next ∧ child next .NeedMore

/-- Complete-input specialization: child contracts exclude incompleteness. -/
def repeatNComplete {α : Type} (child : Cursor → ParseResult α → Prop) (count : Nat)
    (cursor : Cursor) (result : ParseResult (alloc.vec.Vec α)) : Prop :=
  repeatN (fun start => completed (child start)) count cursor (completedResult result)

end RustHammer.Spec
