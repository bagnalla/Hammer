import RustHammer.PartialSpec

open Aeneas Aeneas.Std

namespace RustHammer
open Code

namespace Partial

/-- Output selection is sequencing followed by a pure projection. All children
must succeed, and the selected value keeps the full sequence's final cursor. -/
def left {α β : Type} (first : Cursor → ParseOutcome α → Prop)
    (second : Cursor → ParseOutcome β → Prop) :=
  map (sequence first second) (fun pair value => value = pair.1)

def right {α β : Type} (first : Cursor → ParseOutcome α → Prop)
    (second : Cursor → ParseOutcome β → Prop) :=
  map (sequence first second) (fun pair value => value = pair.2)

def middle {α β γ : Type} (before : Cursor → ParseOutcome α → Prop)
    (child : Cursor → ParseOutcome β → Prop) (after : Cursor → ParseOutcome γ → Prop) :=
  map (sequence before (sequence child after)) (fun pair value => value = pair.2.1)

/-- Ignoring changes only the value; it preserves consumption and both failure outcomes. -/
def ignore {α : Type} (child : Cursor → ParseOutcome α → Prop) :=
  map child (fun _ value => value = ())

end Partial

namespace Spec

def left {α β : Type} (first : Cursor → ParseResult α → Prop)
    (second : Cursor → ParseResult β → Prop) :=
  map (sequence first second) (fun pair value => value = pair.1)

def right {α β : Type} (first : Cursor → ParseResult α → Prop)
    (second : Cursor → ParseResult β → Prop) :=
  map (sequence first second) (fun pair value => value = pair.2)

def middle {α β γ : Type} (before : Cursor → ParseResult α → Prop)
    (child : Cursor → ParseResult β → Prop) (after : Cursor → ParseResult γ → Prop) :=
  map (sequence before (sequence child after)) (fun pair value => value = pair.2.1)

def ignore {α : Type} (child : Cursor → ParseResult α → Prop) :=
  map child (fun _ value => value = ())

end Spec
end RustHammer
