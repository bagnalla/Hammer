import RustHammer.IterationSpec
import RustHammer.FoldRepeatSpec

open RustHammer.Code.grammar.repeat
  RustHammer.Code.input_types

open Aeneas Aeneas.Std

namespace RustHammer.Spec
open Code

abbrev validSepBy {P S : Type} (parser : SepBy P S) := validRepeatBounds parser.bounds
abbrev validFoldSepBy {P S I F : Type} (parser : FoldSepBy P S I F) := validRepeatBounds parser.bounds

def sepByNewOutcome {P S : Type} (parser : P) (separator : S) (min max : Usize)
    (result : core.result.Result (SepBy P S) ConfigError) : Prop :=
  if min.val ≤ max.val then result = .Ok { parser, separator, bounds := { min, max := some max } }
  else result = .Err .InvalidBounds

def foldSepByNewOutcome {P S I F : Type} (parser : P) (separator : S) (min max : Usize)
    (init : I) (fold : F) (result : core.result.Result (FoldSepBy P S I F) ConfigError) : Prop :=
  if min.val ≤ max.val then result = .Ok { parser, separator, bounds := { min, max := some max }, init, fold }
  else result = .Err .InvalidBounds

/-- A separator followed by an item, retaining only the item. No item is attempted
when its separator rejects or needs more input. The separator's value is arbitrary. -/
def separatedTail {α β : Type} (item : Cursor → ParseOutcome α → Prop)
    (separator : Cursor → ParseOutcome β → Prop) (cursor : Cursor) (outcome : ParseOutcome α) : Prop :=
  match outcome with
  | .Success next value => ∃ middle ignored,
      separator cursor (.Success middle ignored) ∧ item middle (.Success next value)
  | .Error error => separator cursor (.Error error) ∨ ∃ middle ignored,
      separator cursor (.Success middle ignored) ∧ item middle (.Error error)
  | .NeedMore => separator cursor .NeedMore ∨ ∃ middle ignored,
      separator cursor (.Success middle ignored) ∧ item middle .NeedMore

/-- First parse an item alone; subsequent attempts parse a whole separator/item
pair. The index counts retained items, not input bytes or separator successes. -/
def separatedAttempt {α β : Type} (item : Cursor → ParseOutcome α → Prop)
    (separator : Cursor → ParseOutcome β → Prop) (count : Nat)
    (cursor : Cursor) (outcome : ParseOutcome α) : Prop :=
  if count = 0 then item cursor outcome else separatedTail item separator cursor outcome

def boundedSepBy {α β : Type} (item : Cursor → ParseOutcome α → Prop)
    (separator : Cursor → ParseOutcome β → Prop) (min max : Nat)
    (cursor : Cursor) (outcome : ParseOutcome (alloc.vec.Vec α)) : Prop :=
  boundedIterations (separatedAttempt item separator) min max cursor (collectedValues outcome)

def unboundedSepBy {α β : Type} (input : Slice U8) (item : Cursor → ParseOutcome α → Prop)
    (separator : Cursor → ParseOutcome β → Prop) (min : Nat)
    (cursor : Cursor) (outcome : ParseOutcome (alloc.vec.Vec α)) : Prop :=
  unboundedIterations input (separatedAttempt item separator) min cursor (collectedValues outcome)

def boundedFoldSepBy {α β R : Type} (item : Cursor → ParseOutcome α → Prop)
    (separator : Cursor → ParseOutcome β → Prop) (initial : R → Prop) (fold : R → α → R → Prop)
    (min max : Nat) (cursor : Cursor) (outcome : ParseOutcome R) : Prop :=
  accumulated (folds initial fold) (boundedIterations (separatedAttempt item separator) min max cursor) outcome

def unboundedFoldSepBy {α β R : Type} (input : Slice U8) (item : Cursor → ParseOutcome α → Prop)
    (separator : Cursor → ParseOutcome β → Prop) (initial : R → Prop) (fold : R → α → R → Prop)
    (min : Nat) (cursor : Cursor) (outcome : ParseOutcome R) : Prop :=
  accumulated (folds initial fold) (unboundedIterations input (separatedAttempt item separator) min cursor) outcome

def boundedSepByComplete {α β : Type} (item : Cursor → ParseResult α → Prop)
    (separator : Cursor → ParseResult β → Prop) (min max : Nat)
    (cursor : Cursor) (result : ParseResult (alloc.vec.Vec α)) : Prop :=
  boundedSepBy (fun start => completed (item start)) (fun start => completed (separator start))
    min max cursor (completedResult result)

def unboundedSepByComplete {α β : Type} (input : Slice U8) (item : Cursor → ParseResult α → Prop)
    (separator : Cursor → ParseResult β → Prop) (min : Nat)
    (cursor : Cursor) (result : ParseResult (alloc.vec.Vec α)) : Prop :=
  unboundedSepBy input (fun start => completed (item start)) (fun start => completed (separator start))
    min cursor (completedResult result)

def boundedFoldSepByComplete {α β R : Type} (item : Cursor → ParseResult α → Prop)
    (separator : Cursor → ParseResult β → Prop) (initial : R → Prop) (fold : R → α → R → Prop)
    (min max : Nat) (cursor : Cursor) (result : ParseResult R) : Prop :=
  boundedFoldSepBy (fun start => completed (item start)) (fun start => completed (separator start))
    initial fold min max cursor (completedResult result)

def unboundedFoldSepByComplete {α β R : Type} (input : Slice U8) (item : Cursor → ParseResult α → Prop)
    (separator : Cursor → ParseResult β → Prop) (initial : R → Prop) (fold : R → α → R → Prop)
    (min : Nat) (cursor : Cursor) (result : ParseResult R) : Prop :=
  unboundedFoldSepBy input (fun start => completed (item start)) (fun start => completed (separator start))
    initial fold min cursor (completedResult result)

end RustHammer.Spec
