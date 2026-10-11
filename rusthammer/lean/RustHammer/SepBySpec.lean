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
def separatedTail {α β : Type} (item : Cursor → Spec.ParseResult α → Prop)
    (separator : Cursor → Spec.ParseResult β → Prop) (cursor : Cursor) (outcome : Spec.ParseResult α) : Prop :=
  match outcome with
  | .Ok (next, value) => ∃ middle ignored,
      separator cursor (.Ok (middle, ignored)) ∧ item middle (.Ok (next, value))
  | .Err error => separator cursor (.Err error) ∨ ∃ middle ignored,
      separator cursor (.Ok (middle, ignored)) ∧ item middle (.Err error)
/-- First parse an item alone; subsequent attempts parse a whole separator/item
pair. The index counts retained items, not input bytes or separator successes. -/
def separatedAttempt {α β : Type} (item : Cursor → Spec.ParseResult α → Prop)
    (separator : Cursor → Spec.ParseResult β → Prop) (count : Nat)
    (cursor : Cursor) (outcome : Spec.ParseResult α) : Prop :=
  if count = 0 then item cursor outcome else separatedTail item separator cursor outcome

def boundedSepBy {α β : Type} (item : Cursor → Spec.ParseResult α → Prop)
    (separator : Cursor → Spec.ParseResult β → Prop) (min max : Nat)
    (cursor : Cursor) (outcome : Spec.ParseResult (alloc.vec.Vec α)) : Prop :=
  boundedIterations (separatedAttempt item separator) min max cursor (collectedValues outcome)

def unboundedSepBy {α β : Type} (input : Slice U8) (item : Cursor → Spec.ParseResult α → Prop)
    (separator : Cursor → Spec.ParseResult β → Prop) (min : Nat)
    (cursor : Cursor) (outcome : Spec.ParseResult (alloc.vec.Vec α)) : Prop :=
  unboundedIterations input (separatedAttempt item separator) min cursor (collectedValues outcome)

def boundedFoldSepBy {α β R : Type} (item : Cursor → Spec.ParseResult α → Prop)
    (separator : Cursor → Spec.ParseResult β → Prop) (initial : R → Prop) (fold : R → α → R → Prop)
    (min max : Nat) (cursor : Cursor) (outcome : Spec.ParseResult R) : Prop :=
  accumulated (folds initial fold) (boundedIterations (separatedAttempt item separator) min max cursor) outcome

def unboundedFoldSepBy {α β R : Type} (input : Slice U8) (item : Cursor → Spec.ParseResult α → Prop)
    (separator : Cursor → Spec.ParseResult β → Prop) (initial : R → Prop) (fold : R → α → R → Prop)
    (min : Nat) (cursor : Cursor) (outcome : Spec.ParseResult R) : Prop :=
  accumulated (folds initial fold) (unboundedIterations input (separatedAttempt item separator) min cursor) outcome

def boundedSepByComplete {α β : Type} (item : Cursor → ParseResult α → Prop)
    (separator : Cursor → ParseResult β → Prop) (min max : Nat)
    (cursor : Cursor) (result : ParseResult (alloc.vec.Vec α)) : Prop :=
  boundedSepBy (fun start => satisfies (item start)) (fun start => satisfies (separator start))
    min max cursor (result)

def unboundedSepByComplete {α β : Type} (input : Slice U8) (item : Cursor → ParseResult α → Prop)
    (separator : Cursor → ParseResult β → Prop) (min : Nat)
    (cursor : Cursor) (result : ParseResult (alloc.vec.Vec α)) : Prop :=
  unboundedSepBy input (fun start => satisfies (item start)) (fun start => satisfies (separator start))
    min cursor (result)

def boundedFoldSepByComplete {α β R : Type} (item : Cursor → ParseResult α → Prop)
    (separator : Cursor → ParseResult β → Prop) (initial : R → Prop) (fold : R → α → R → Prop)
    (min max : Nat) (cursor : Cursor) (result : ParseResult R) : Prop :=
  boundedFoldSepBy (fun start => satisfies (item start)) (fun start => satisfies (separator start))
    initial fold min max cursor (result)

def unboundedFoldSepByComplete {α β R : Type} (input : Slice U8) (item : Cursor → ParseResult α → Prop)
    (separator : Cursor → ParseResult β → Prop) (initial : R → Prop) (fold : R → α → R → Prop)
    (min : Nat) (cursor : Cursor) (result : ParseResult R) : Prop :=
  unboundedFoldSepBy input (fun start => satisfies (item start)) (fun start => satisfies (separator start))
    initial fold min cursor (result)

end RustHammer.Spec
