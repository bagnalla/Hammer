import RustHammer.Rusthammer

open RustHammer.Code.input_types
  RustHammer.Code.parser_traits

open Aeneas Aeneas.Std Result

/-! Direct-execution views of the extracted evaluators. These definitions only
specialize the backend to `Direct` and discard its unit state; they contain no
separate parser implementation. The grammar specifications remain independent
of this representation detail. -/
namespace RustHammer.Code

abbrev DirectParser (P α : Type) := Eval P Direct α

def DirectParser.parse_with {P α : Type} (inst : DirectParser P α)
    (parser : P) (input : Slice U8) (cursor : Cursor) (context : ParseContext) :
    Result (ParseOutcome α) := do
  let (outcome, _) ← inst.eval parser () input cursor context
  ok outcome

def DirectParser.parse {P α : Type} (inst : DirectParser P α)
    (parser : P) (input : Slice U8) (cursor : Cursor) := do
  let outcome ← inst.parse_with parser input cursor ParseContext.FINAL
  ParseOutcome.into_complete outcome

theorem eval_direct {P α : Type} (inst : DirectParser P α)
    (parser : P) (input : Slice U8) (cursor : Cursor) (context : ParseContext) :
    inst.eval parser () input cursor context = (do
      let outcome ← inst.parse_with parser input cursor context
      ok (outcome, ())) := by
  unfold DirectParser.parse_with
  rw [Std.bind_assoc]
  conv_lhs => rw [← Std.bind_pure (inst.eval parser () input cursor context)]
  apply congrArg (Std.bind (inst.eval parser () input cursor context))
  funext ⟨outcome, state⟩
  cases state
  simp [bind_ok]

theorem direct_entry_with {P α : Type} (inst : DirectParser P α)
    (parser : P) (input : Slice U8) (cursor : Cursor) (context : ParseContext) :
    Parser.parse_with.default (Parser.Blanket inst) parser input cursor context =
      inst.parse_with parser input cursor context := rfl

theorem direct_entry {P α : Type} (inst : DirectParser P α)
    (parser : P) (input : Slice U8) (cursor : Cursor) :
    Parser.parse.default (Parser.Blanket inst) parser input cursor =
      inst.parse parser input cursor := rfl

/-- Projecting the empty direct state preserves any outcome contract. -/
theorem direct_projection_spec {α : Type} (result : Result (α × Direct))
    (post : α → Prop) (h : result ⦃ pair => post pair.1 ⦄) :
    (do let (value, _) ← result; ok value) ⦃ value => post value ⦄ := by
  apply WP.spec_bind h
  rintro ⟨value, state⟩ hp
  simpa using hp

end RustHammer.Code

register_simp_attr direct_lift
