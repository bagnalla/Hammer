import RustHammer.SeekArithmetic

open Aeneas Aeneas.Std Result WP
open RustHammer.Code.input_types RustHammer.Code.grammar.position
open RustHammer.Code.parser_traits

namespace RustHammer.Seeking
open Code Proofs

theorem to_spec (target : Cursor) :
    Seek.to target ⦃ result => result = if target.bit.val < 8 then
      .Ok ⟨.Absolute target⟩ else .Err .InvalidBitOffset ⦄ := by
  unfold Seek.to
  split <;> simp [spec_ok] <;> scalar_tac

theorem relative_spec (offset : Isize) :
    Seek.relative offset ⦃ result => result = ⟨.Relative offset⟩ ⦄ := by
  simp [Seek.relative, spec_ok]

theorem from_end_spec (offset : Isize) :
    Seek.from_end offset ⦃ result => result = ⟨.End offset⟩ ⦄ := by
  simp [Seek.from_end, spec_ok]

theorem to_valid (target : Cursor) :
    Seek.to target ⦃ result => ∀ parser, result = .Ok parser → valid parser ⦄ := by
  step with to_spec target as ⟨result, hresult⟩
  rename_i parser heq
  split at hresult
  · rename_i hbit
    cases hresult.symm.trans heq
    exact hbit
  · cases hresult.symm.trans heq

theorem clone_spec (parser : Seek) :
    Seek.Insts.CoreCloneClone.clone parser ⦃ copied => copied = parser ⦄ := by
  simp [Seek.Insts.CoreCloneClone.clone, spec_ok]

theorem position_spec (parser : Seek) (length : Usize) (cursor : Cursor)
    (status : InputStatus) (hp : valid parser) :
    seek_position parser length cursor status
      ⦃ result => outcome parser length.val cursor status result ⦄ := by
  unfold seek_position
  step with advance_cursor_zero_spec length cursor as ⟨checked, hchecked⟩
  by_cases hv : Spec.validPosition length.val cursor
  · simp only [if_pos hv] at hchecked
    simp only [hchecked]
    rcases parser with ⟨target⟩
    cases target with
    | Absolute target =>
      step with advance_cursor_zero_spec length target as ⟨advanced, hadvanced⟩
      have hnonneg : ¬(Spec.position target : Int) < 0 := by omega
      by_cases ht : Spec.validPosition length.val target
      · simp only [if_pos ht] at hadvanced
        simp only [hadvanced, bind_ok]
        step with classify_spec status (.Ok (target, target)) as ⟨result, hresult⟩
        have hin : ¬(8 * length.val : Nat) < (Spec.position target : Int) := by
          have := ht.2; omega
        simp only [outcome, if_pos hv, awaitsEnd, if_false]
        exact ⟨.Ok target, by
          simp only [targetOutcome, if_pos hv, targetPosition, if_neg hnonneg, if_neg hin]
          exact ⟨target, rfl, ht, rfl⟩, hresult⟩
      · simp only [if_neg ht] at hadvanced
        simp only [hadvanced, bind_ok]
        step with classify_spec status (.Err .UnexpectedEnd) as ⟨result, hresult⟩
        have hout : (8 * length.val : Nat) < (Spec.position target : Int) := by
          have hbit : target.bit.val < 8 := hp
          unfold Spec.validPosition at ht
          omega
        simp only [outcome, if_pos hv, awaitsEnd, if_false]
        exact ⟨.Err .UnexpectedEnd, by
          simp only [targetOutcome, if_pos hv, targetPosition, if_neg hnonneg, if_pos hout], hresult⟩
    | Relative offset =>
      step with offset_cursor_spec length cursor offset as ⟨raw, hraw⟩
      cases raw with
      | Ok next =>
        step with classify_spec status (.Ok (next, next)) as ⟨result, hresult⟩
        simp only [outcome, if_pos hv, awaitsEnd, if_false]
        exact ⟨.Ok next, hraw, hresult⟩
      | Err error =>
        step with classify_spec status (.Err error) as ⟨result, hresult⟩
        simp only [outcome, if_pos hv, awaitsEnd, if_false]
        exact ⟨.Err error, hraw, hresult⟩
    | End offset =>
      cases status with
      | Partial => simpa [outcome, awaitsEnd, spec_ok] using hv
      | Final =>
        have hend : Spec.validPosition length.val { byte := length, bit := 0#u8 } := by
          simp [Spec.validPosition, Spec.position]
        step with offset_cursor_spec length { byte := length, bit := 0#u8 } offset as ⟨raw, hraw⟩
        have htarget : targetOutcome length.val cursor
            (targetPosition (.End offset) length.val cursor) raw := by
          simpa only [targetOutcome, if_pos hv, if_pos hend, targetPosition,
            Spec.position, UScalar.ofNatCore_val_eq, Nat.add_zero] using hraw
        cases raw with
        | Ok next =>
          step with classify_spec .Final (.Ok (next, next)) as ⟨result, hresult⟩
          simp only [outcome, if_pos hv, awaitsEnd, if_false]
          exact ⟨.Ok next, htarget, hresult⟩
        | Err error =>
          step with classify_spec .Final (.Err error) as ⟨result, hresult⟩
          simp only [outcome, if_pos hv, awaitsEnd, if_false]
          exact ⟨.Err error, htarget, hresult⟩
  · simp only [if_neg hv] at hchecked
    simp [hchecked, outcome, hv, spec_ok]

abbrev evalInst (State : Type) := Seek.Insts.RusthammerParser_traitsEvalInputBackendCursor State

/-- Seeking changes neither backend state nor context and reads no bytes. The
contract holds for every ordering context, including malformed entry cursors. -/
theorem eval_spec {State : Type} (parser : Seek) (state : State) (input : Slice U8)
    (cursor : Cursor) (context : ParseContext) (hp : valid parser) :
    (evalInst State).eval parser state input cursor context
      ⦃ result => outcome parser input.val.length cursor context.status result.1 ∧ result.2 = state ⦄ := by
  unfold evalInst Seek.Insts.RusthammerParser_traitsEvalInputBackendCursor
    Seek.Insts.RusthammerParser_traitsEvalInputBackendCursor.eval
  step with position_spec parser input.len cursor context.status hp as ⟨result, hresult⟩
  exact hresult

theorem with_spec (parser : Seek) (input : Slice U8) (cursor : Cursor)
    (context : ParseContext) (hp : valid parser) :
    DirectParser.parse_with (evalInst Direct) parser input cursor context
      ⦃ result => outcome parser input.val.length cursor context.status result ⦄ := by
  unfold DirectParser.parse_with
  step with eval_spec parser () input cursor context hp as ⟨pair, hpair⟩
  exact hpair

/-- The public blanket Parser entry executes the same verified evaluator. -/
theorem entry_with_spec (parser : Seek) (input : Slice U8) (cursor : Cursor)
    (context : ParseContext) (hp : valid parser) :
    Parser.parse_with.default (Parser.Blanket (evalInst Direct)) parser input cursor context
      ⦃ result => outcome parser input.val.length cursor context.status result ⦄ := by
  exact with_spec parser input cursor context hp

end RustHammer.Seeking
