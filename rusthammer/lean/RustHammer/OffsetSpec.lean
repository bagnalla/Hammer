import RustHammer.SeekSpec
import RustHammer.ByteSpec
import RustHammer.BindSpec
import RustHammer.SelectionSpec

open Aeneas Aeneas.Std
open RustHammer.Code.input_types

namespace RustHammer.Offset
open Code

/-- The byte offset is measured from the end of the displacement field. The
specification uses an unbounded mathematical destination, not a machine cast. -/
def jump (input : Slice U8) (cursor : Cursor) (distance : Nat) (status : InputStatus)
    (result : ParseOutcome Cursor) : Prop :=
  ∃ raw, Seeking.targetOutcome input.val.length cursor
    ((Spec.position cursor : Int) + 8 * distance) raw ∧
    result = Partial.primitiveResult status (Seeking.reported raw)

def body (input : Slice U8) (cursor : Cursor) (distance : Nat) (status : InputStatus) :=
  Partial.right (fun start => jump input start distance status)
    (fun start => Partial.primitive status (Spec.takeAlignedOutcome input start 2#usize)) cursor

/-- A displacement byte, skipped bytes, then a borrowed two-byte payload.
Skipped and trailing bytes are unconstrained. This is a prefix grammar. -/
def payload (input : Slice U8) (cursor : Cursor) (status : InputStatus) :=
  Partial.bind (fun start => Partial.primitive status (Spec.byteOutcome input start))
    (fun distance start => body input start distance.val status) cursor

end RustHammer.Offset
