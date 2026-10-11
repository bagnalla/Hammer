import RustHammer.ControlSpec

open RustHammer.Code.grammar.transform
  RustHammer.Code.input_types

open Aeneas Aeneas.Std

namespace RustHammer
open Code

namespace Spec

/-- Output selection is sequencing followed by a pure projection. All children
must succeed, and the selected value keeps the full sequence's final cursor. -/
def left {α β : Type} (first : Cursor → Spec.ParseResult α → Prop)
    (second : Cursor → Spec.ParseResult β → Prop) :=
  map (sequence first second) (fun pair value => value = pair.1)

def right {α β : Type} (first : Cursor → Spec.ParseResult α → Prop)
    (second : Cursor → Spec.ParseResult β → Prop) :=
  map (sequence first second) (fun pair value => value = pair.2)

def middle {α β γ : Type} (before : Cursor → Spec.ParseResult α → Prop)
    (child : Cursor → Spec.ParseResult β → Prop) (after : Cursor → Spec.ParseResult γ → Prop) :=
  map (sequence before (sequence child after)) (fun pair value => value = pair.2.1)

/-- Ignoring changes only the value; it preserves consumption and errors. -/
def ignore {α : Type} (child : Cursor → Spec.ParseResult α → Prop) :=
  map child (fun _ value => value = ())

end Spec
end RustHammer
