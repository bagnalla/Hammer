import RustHammer.SepBySpec
import RustHammer.RepeatDriverProofs
import RustHammer.SelectionProofs

open Aeneas Aeneas.Std Result WP

namespace RustHammer.Proofs
open Code

/-- Output selection implements the independent separator/item contract. -/
theorem separated_tail_of_right {α β : Type} (item : Cursor → ParseOutcome α → Prop)
    (separator : Cursor → ParseOutcome β → Prop) (cursor : Cursor) (outcome : ParseOutcome α)
    (h : Partial.right separator item cursor outcome) : Spec.separatedTail item separator cursor outcome := by
  rcases h with ⟨parsed, hsequence, hmapped⟩
  rcases hsequence with ⟨separated, hseparator, hitem⟩
  cases separated with
  | NeedMore => cases hitem; cases hmapped; exact Or.inl hseparator
  | Error error => cases hitem; cases hmapped; exact Or.inl hseparator
  | Success middle ignored =>
    rcases hitem with ⟨child, hchild, hpair⟩
    cases child with
    | NeedMore => cases hpair; cases hmapped; exact Or.inr ⟨middle, ignored, hseparator, hchild⟩
    | Error error => cases hpair; cases hmapped; exact Or.inr ⟨middle, ignored, hseparator, hchild⟩
    | Success next value =>
      cases hpair
      rcases hmapped with ⟨mapped, rfl, rfl⟩
      exact ⟨middle, ignored, hseparator, hchild⟩

theorem separated_attempt_spec {P S α β : Type} (pi : DirectParser P α) (si : DirectParser S β)
    (parser : P) (separator : S) (count : Usize) (input : Slice U8) (cursor : Cursor) (context : ParseContext)
    (item : Cursor → ParseOutcome α → Prop) (sep : Cursor → ParseOutcome β → Prop)
    (hp : ∀ start, pi.parse_with parser input start context ⦃ result => item start result ⦄)
    (hs : ∀ start, si.parse_with separator input start context ⦃ result => sep start result ⦄) :
    DirectRun.repeat_parse pi (Right.Insts.RusthammerParser (Shared0P.Insts.RusthammerParser si)
      (Shared0P.Insts.RusthammerParser pi)) parser { first := separator, second := parser }
      count input cursor context ⦃ result => Spec.separatedAttempt item sep count.val cursor result ⦄ := by
  rw [DirectRun.repeat_parse_eq]
  by_cases hzero : count = 0#usize
  · simpa [hzero, Spec.separatedAttempt] using hp cursor
  · have hn : count.val ≠ 0 := by scalar_tac
    simp only [hzero, ↓reduceIte, Spec.separatedAttempt, hn]
    change Right.Insts.RusthammerParser.parse_with (Shared0P.Insts.RusthammerParser si)
      (Shared0P.Insts.RusthammerParser pi) { first := separator, second := parser }
      input cursor context ⦃ result => Spec.separatedTail item sep cursor result ⦄
    step with right_with_spec (Shared0P.Insts.RusthammerParser si) (Shared0P.Insts.RusthammerParser pi)
      { first := separator, second := parser } input cursor context sep item hs hp as ⟨outcome, houtcome⟩
    exact separated_tail_of_right item sep cursor outcome houtcome

/-- Complete-input child contracts make incomplete separator/item attempts impossible. -/
theorem separated_attempt_complete_not_need_more {α β : Type}
    (item : Cursor → Spec.ParseResult α → Prop) (sep : Cursor → Spec.ParseResult β → Prop)
    (count : Nat) (cursor : Cursor) :
    ¬Spec.separatedAttempt (fun c => Spec.completed (item c))
      (fun c => Spec.completed (sep c)) count cursor .NeedMore := by
  have hc {γ : Type} (contract : Spec.ParseResult γ → Prop) : ¬Spec.completed contract .NeedMore := by
    rintro ⟨result, _, heq⟩
    cases result with
    | Err _ => cases heq
    | Ok pair => cases pair; cases heq
  unfold Spec.separatedAttempt
  split
  · exact hc _
  · rintro (h | ⟨_, _, _, h⟩)
    · exact hc _ h
    · exact hc _ h

end RustHammer.Proofs
