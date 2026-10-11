import RustHammer.SepBySpec
import RustHammer.RepeatDriverProofs
import RustHammer.SelectionProofs

open RustHammer.Code.grammar.sequence
  RustHammer.Code.input_types

open Aeneas Aeneas.Std Result WP

namespace RustHammer.Proofs
open Code

/-- Output selection implements the independent separator/item contract. -/
theorem separated_tail_of_right {α β : Type} (item : Cursor → Spec.ParseResult α → Prop)
    (separator : Cursor → Spec.ParseResult β → Prop) (cursor : Cursor) (outcome : Spec.ParseResult α)
    (h : Contracts.right separator item cursor outcome) : Spec.separatedTail item separator cursor outcome := by
  rcases h with ⟨parsed, hsequence, hmapped⟩
  rcases hsequence with ⟨separated, hseparator, hitem⟩
  cases separated with
  | Err error => cases hitem; cases hmapped; exact Or.inl hseparator
  | Ok pair =>
    rcases pair with ⟨middle, ignored⟩
    rcases hitem with ⟨child, hchild, hpair⟩
    cases child with
    | Err error => cases hpair; cases hmapped; exact Or.inr ⟨middle, ignored, hseparator, hchild⟩
    | Ok pair =>
      rcases pair with ⟨next, value⟩
      cases hpair
      rcases hmapped with ⟨mapped, rfl, rfl⟩
      exact ⟨middle, ignored, hseparator, hchild⟩

theorem separated_attempt_spec {P S α β : Type} (pi : parser_traits.Parser P α) (si : parser_traits.Parser S β)
    (parser : P) (separator : S) (count : Usize) (input : Slice U8) (cursor : Cursor) (context : ByteOrder)
    (item : Cursor → Spec.ParseResult α → Prop) (sep : Cursor → Spec.ParseResult β → Prop)
    (hp : ∀ start, pi.parse_with parser input start context ⦃ result => item start result ⦄)
    (hs : ∀ start, si.parse_with separator input start context ⦃ result => sep start result ⦄) :
    grammar.repeat.repeat_parse pi (Right.Insts.RusthammerParser_traitsParser (Shared0P.Insts.RusthammerParser_traitsParser si)
      (Shared0P.Insts.RusthammerParser_traitsParser pi)) parser { first := separator, second := parser }
      count input cursor context ⦃ result => Spec.separatedAttempt item sep count.val cursor result ⦄ := by
  rw [grammar.repeat.repeat_parse]
  by_cases hzero : count = 0#usize
  · simpa [hzero, Spec.separatedAttempt] using hp cursor
  · have hn : count.val ≠ 0 := by scalar_tac
    simp only [hzero, ↓reduceIte, Spec.separatedAttempt, hn]
    change Right.Insts.RusthammerParser_traitsParser.parse_with (Shared0P.Insts.RusthammerParser_traitsParser si)
      (Shared0P.Insts.RusthammerParser_traitsParser pi) { first := separator, second := parser }
      input cursor context ⦃ result => Spec.separatedTail item sep cursor result ⦄
    step with right_with_spec (Shared0P.Insts.RusthammerParser_traitsParser si) (Shared0P.Insts.RusthammerParser_traitsParser pi)
      { first := separator, second := parser } input cursor context sep item hs hp as ⟨outcome, houtcome⟩
    exact separated_tail_of_right item sep cursor outcome houtcome

end RustHammer.Proofs
