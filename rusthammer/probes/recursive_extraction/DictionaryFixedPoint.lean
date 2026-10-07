module
public import Aeneas

/-!
Handwritten target-language experiment for `backend_recursive_trait.rs`.
This is not Aeneas output and is not an extraction/correctness proof for RustHammer.
It checks that an explicit function fixed point can contain a method dictionary.
-/
@[expose] public section
open Aeneas Aeneas.Std Result Lean.Order
set_option linter.unusedVariables false
namespace RecursiveDictionaryModel

structure Eval (Self B : Type) where
  eval : Self → B → U8 → Result (U8 × B)

def body {B : Type} (rule : Eval Unit B) (backend : B) (count : U8) :
    Result (U8 × B) := do
  if count = 0#u8 then
    ok (0#u8, backend)
  else
    let n ← count - 1#u8
    rule.eval () backend n

def eval (self backend : Unit) (count : U8) : Result (U8 × Unit) :=
  body { eval := eval } backend count
partial_fixpoint monotonicity by
  intro f g h self backend count
  dsimp [body]
  split
  · exact PartialOrder.rel_refl
  · exact MonoBind.bind_mono_right (fun n => h () backend n)

@[reducible] def rule : Eval Unit Unit := { eval := eval }

theorem rule_unfold (backend : Unit) (count : U8) :
    rule.eval () backend count = body rule backend count := by
  exact eval.eq_def () backend count

#print axioms rule_unfold

end RecursiveDictionaryModel
