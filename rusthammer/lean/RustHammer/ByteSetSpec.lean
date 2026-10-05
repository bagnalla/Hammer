import RustHammer.ByteSpec

open Aeneas Aeneas.Std

namespace RustHammer.Spec
open Code

/-- One bit per byte value, expressed using mathematical word values. Every
four-word bitmap is a valid set; this is not a constructor-only invariant. -/
def bitmapMember (words : Array U64 4#usize) (value : U8) : Prop :=
  words[value.val / 64]!.val.testBit (value.val % 64) = true

instance (words : Array U64 4#usize) : DecidablePred (bitmapMember words) :=
  fun _ => by unfold bitmapMember; infer_instance

/-- Connect the owned representation to a caller's original mathematical set. -/
def bitmapRepresents (set : ByteSet) (bytes : List U8) : Prop :=
  ∀ value, bitmapMember set.words value ↔ value ∈ bytes

/-- The acceptance predicate of an arbitrary owned bitmap. -/
def bitmapPredicate (set : ByteSet) (excluded : Bool) (value : U8) : Prop :=
  if excluded then ¬ bitmapMember set.words value else bitmapMember set.words value

instance (set : ByteSet) (excluded : Bool) : DecidablePred (bitmapPredicate set excluded) :=
  fun _ => by unfold bitmapPredicate; infer_instance

abbrev bitmapOutcome (input : Slice U8) (status : InputStatus)
    (set : ByteSet) (excluded : Bool) :=
  Partial.verify (fun cursor => Partial.primitive status (byteOutcome input cursor))
    (bitmapPredicate set excluded)

abbrev bitmapComplete (input : Slice U8) (set : ByteSet) (excluded : Bool) :=
  verify (byteOutcome input) (bitmapPredicate set excluded)

/-- Literal list membership; order and duplicates have no semantic effect.
Exclusion negates only the predicate, after a byte has been decoded. -/
def byteSetPredicate (bytes : List U8) (excluded : Bool) (value : U8) : Prop :=
  if excluded then value ∉ bytes else value ∈ bytes

instance (bytes : List U8) (excluded : Bool) : DecidablePred (byteSetPredicate bytes excluded) :=
  fun value => by unfold byteSetPredicate; infer_instance

/-- A set parser inherits all byte decoding, cursor, and finality rules. -/
abbrev byteSetOutcome (input : Slice U8) (status : InputStatus)
    (bytes : List U8) (excluded : Bool) :=
  Partial.verify (fun cursor => Partial.primitive status (byteOutcome input cursor))
    (byteSetPredicate bytes excluded)

abbrev byteSetComplete (input : Slice U8) (bytes : List U8) (excluded : Bool) :=
  verify (byteOutcome input) (byteSetPredicate bytes excluded)

end RustHammer.Spec
