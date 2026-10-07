import RustHammer.MatchSpec
import RustHammer.PartialProofs

open RustHammer.Code.grammar.control
  RustHammer.Code.input_types

open Aeneas Aeneas.Std Result WP

namespace RustHammer.Proofs
open Code

theorem match_length_allows_spec (first second : Cursor) (allowEqual : Bool) :
    match_length_allows first second allowEqual
      ⦃ result => result = decide (Spec.matchEndpointOrder allowEqual first second) ⦄ := by
  by_cases hb : first.byte > second.byte
  · have hp : Spec.matchEndpointOrder allowEqual first second := Or.inl (by scalar_tac)
    simp [match_length_allows, hb, hp, spec_ok]
  · by_cases heq : first.byte = second.byte
    · by_cases ht : first.bit > second.bit
      · have hp : Spec.matchEndpointOrder allowEqual first second := by
          unfold Spec.matchEndpointOrder
          cases allowEqual <;> scalar_tac
        simp [match_length_allows, heq, ht, hp, spec_ok]
      · cases allowEqual with
        | false =>
          have hn : ¬Spec.matchEndpointOrder false first second := by
            unfold Spec.matchEndpointOrder
            scalar_tac
          simp [match_length_allows, heq, ht, hn, spec_ok]
        | true =>
          have hequiv : Spec.matchEndpointOrder true first second ↔ first.bit = second.bit := by
            unfold Spec.matchEndpointOrder
            scalar_tac
          simp [match_length_allows, heq, ht, hequiv, spec_ok]
    · have hn : ¬Spec.matchEndpointOrder allowEqual first second := by
        unfold Spec.matchEndpointOrder
        cases allowEqual <;> scalar_tac
      simp [match_length_allows, hb, heq, hn, spec_ok]

/-- Normalized endpoints compare the true bit positions without any machine
representation assumption on those absolute positions. -/
theorem match_endpoint_order_bits (allowEqual : Bool) (first second : Cursor)
    (hf : first.bit.val < 8) (hs : second.bit.val < 8) :
    Spec.matchEndpointOrder allowEqual first second ↔
      if allowEqual then Spec.position second ≤ Spec.position first
      else Spec.position second < Spec.position first := by
  unfold Spec.matchEndpointOrder Spec.position
  cases allowEqual <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

/-- For two forward matches from one start, endpoint order is consumed-length order. -/
theorem match_endpoint_order_consumption (allowEqual : Bool) (cursor first second : Cursor)
    (hf : first.bit.val < 8) (hs : second.bit.val < 8)
    (hcf : Spec.position cursor ≤ Spec.position first)
    (hcs : Spec.position cursor ≤ Spec.position second) :
    Spec.matchEndpointOrder allowEqual first second ↔
      if allowEqual then Spec.position second - Spec.position cursor ≤ Spec.position first - Spec.position cursor
      else Spec.position second - Spec.position cursor < Spec.position first - Spec.position cursor := by
  rw [match_endpoint_order_bits allowEqual first second hf hs]
  cases allowEqual <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

theorem restrict_match_with_spec {P Q α β : Type} (pi : DirectParser P α) (qi : DirectParser Q β)
    (p : P) (q : Q) (input : Slice U8) (cursor : Cursor) (context : ParseContext) (allowEqual : Bool)
    (first : Cursor → ParseOutcome α → Prop) (second : Cursor → ParseOutcome β → Prop)
    (hp : pi.parse_with p input cursor context ⦃ result => first cursor result ⦄)
    (hq : qi.parse_with q input cursor context ⦃ result => second cursor result ⦄) :
    DirectRun.restrict_match pi qi p q input cursor context allowEqual
      ⦃ result => Partial.matchRestriction allowEqual first second cursor result ⦄ := by
  rw [DirectRun.restrict_match_eq]
  step with hp as ⟨left, hleft⟩
  cases left with
  | NeedMore => simp only [spec_ok]; exact ⟨.NeedMore, hleft, rfl⟩
  | Error error => simp only [spec_ok]; exact ⟨.Error error, hleft, rfl⟩
  | Success next value =>
    step with hq as ⟨right, hright⟩
    cases right with
    | NeedMore => simp only [spec_ok]; exact ⟨.Success next value, hleft, .NeedMore, hright, rfl⟩
    | Error error =>
      step with recoverable_spec error as ⟨recover, hrecover⟩
      by_cases hr : Spec.recoverable error
      · have heq : recover = true := by simpa [hr] using hrecover
        simp only [heq, ↓reduceIte, spec_ok]
        exact ⟨.Success next value, hleft, .Error error, hright, by simp [hr]⟩
      · have heq : recover = false := by simpa [hr] using hrecover
        simp only [heq, Bool.false_eq_true, ↓reduceIte, spec_ok]
        exact ⟨.Success next value, hleft, .Error error, hright, by simp [hr]⟩
    | Success other otherValue =>
      step with match_length_allows_spec next other allowEqual as ⟨accepts, haccepts⟩
      by_cases hl : Spec.matchEndpointOrder allowEqual next other
      · have heq : accepts = true := by simpa [hl] using haccepts
        simp only [heq, ↓reduceIte, spec_ok]
        exact ⟨.Success next value, hleft, .Success other otherValue, hright, by simp [hl]⟩
      · have heq : accepts = false := by simpa [hl] using haccepts
        simp only [heq, Bool.false_eq_true, ↓reduceIte, spec_ok]
        exact ⟨.Success next value, hleft, .Success other otherValue, hright, by simp [hl]⟩

theorem but_not_with_spec {P Q α β : Type} (pi : DirectParser P α) (qi : DirectParser Q β)
    (parser : ButNot P Q) (input : Slice U8) (cursor : Cursor) (context : ParseContext)
    (first : Cursor → ParseOutcome α → Prop) (second : Cursor → ParseOutcome β → Prop)
    (hp : pi.parse_with parser.first input cursor context ⦃ result => first cursor result ⦄)
    (hq : qi.parse_with parser.second input cursor context ⦃ result => second cursor result ⦄) :
    ButNot.Insts.RusthammerParser.parse_with pi qi parser input cursor context
      ⦃ result => Partial.matchRestriction false first second cursor result ⦄ := by
  exact restrict_match_with_spec pi qi parser.first parser.second input cursor context false first second hp hq

theorem difference_with_spec {P Q α β : Type} (pi : DirectParser P α) (qi : DirectParser Q β)
    (parser : Difference P Q) (input : Slice U8) (cursor : Cursor) (context : ParseContext)
    (first : Cursor → ParseOutcome α → Prop) (second : Cursor → ParseOutcome β → Prop)
    (hp : pi.parse_with parser.first input cursor context ⦃ result => first cursor result ⦄)
    (hq : qi.parse_with parser.second input cursor context ⦃ result => second cursor result ⦄) :
    Difference.Insts.RusthammerParser.parse_with pi qi parser input cursor context
      ⦃ result => Partial.matchRestriction true first second cursor result ⦄ := by
  exact restrict_match_with_spec pi qi parser.first parser.second input cursor context true first second hp hq

theorem xor_with_spec {P Q α : Type} (pi : DirectParser P α) (qi : DirectParser Q α)
    (parser : Xor P Q) (input : Slice U8) (cursor : Cursor) (context : ParseContext)
    (first second : Cursor → ParseOutcome α → Prop)
    (hp : pi.parse_with parser.first input cursor context ⦃ result => first cursor result ⦄)
    (hq : qi.parse_with parser.second input cursor context ⦃ result => second cursor result ⦄) :
    Xor.Insts.RusthammerParser.parse_with pi qi parser input cursor context
      ⦃ result => Partial.exclusive first second cursor result ⦄ := by
  rw [Xor.Insts.RusthammerParser.parse_with_eq]
  step with hp as ⟨left, hleft⟩
  cases left with
  | NeedMore => simp only [spec_ok]; exact ⟨.NeedMore, hleft, rfl⟩
  | Error error =>
    step with recoverable_spec error as ⟨recover, hrecover⟩
    by_cases hr : Spec.recoverable error
    · have heq : recover = true := by simpa [hr] using hrecover
      simp only [heq, ↓reduceIte]
      step with hq as ⟨right, hright⟩
      exact ⟨.Error error, hleft, by simpa [hr] using hright⟩
    · have heq : recover = false := by simpa [hr] using hrecover
      simp only [heq, Bool.false_eq_true, ↓reduceIte, spec_ok]
      exact ⟨.Error error, hleft, by simp [hr]⟩
  | Success next value =>
    step with hq as ⟨right, hright⟩
    cases right with
    | NeedMore => simp only [spec_ok]; exact ⟨.Success next value, hleft, .NeedMore, hright, rfl⟩
    | Success other otherValue =>
      simp only [spec_ok]
      exact ⟨.Success next value, hleft, .Success other otherValue, hright, rfl⟩
    | Error error =>
      step with recoverable_spec error as ⟨recover, hrecover⟩
      by_cases hr : Spec.recoverable error
      · have heq : recover = true := by simpa [hr] using hrecover
        simp only [heq, ↓reduceIte, spec_ok]
        exact ⟨.Success next value, hleft, .Error error, hright, by simp [hr]⟩
      · have heq : recover = false := by simpa [hr] using hrecover
        simp only [heq, Bool.false_eq_true, ↓reduceIte, spec_ok]
        exact ⟨.Success next value, hleft, .Error error, hright, by simp [hr]⟩

theorem match_restriction_not_more {α β : Type} (allowEqual : Bool)
    (first : Cursor → ParseOutcome α → Prop) (second : Cursor → ParseOutcome β → Prop) (cursor : Cursor)
    (hp : ¬first cursor .NeedMore) (hq : ¬second cursor .NeedMore) :
    ¬Partial.matchRestriction allowEqual first second cursor .NeedMore := by
  rintro ⟨left, hleft, hrest⟩
  cases left with
  | NeedMore => exact hp hleft
  | Error error => cases hrest
  | Success next value =>
    rcases hrest with ⟨right, hright, hrest⟩
    cases right with
    | NeedMore => exact hq hright
    | Error error => dsimp only at hrest; split at hrest <;> cases hrest
    | Success other otherValue => dsimp only at hrest; split at hrest <;> cases hrest

theorem xor_not_more {α : Type} (first second : Cursor → ParseOutcome α → Prop) (cursor : Cursor)
    (hp : ¬first cursor .NeedMore) (hq : ¬second cursor .NeedMore) :
    ¬Partial.exclusive first second cursor .NeedMore := by
  rintro ⟨left, hleft, hrest⟩
  cases left with
  | NeedMore => exact hp hleft
  | Error error =>
    dsimp only at hrest
    split at hrest
    · exact hq hrest
    · cases hrest
  | Success next value =>
    rcases hrest with ⟨right, hright, hrest⟩
    cases right with
    | NeedMore => exact hq hright
    | Error error => dsimp only at hrest; split at hrest <;> cases hrest
    | Success other otherValue => cases hrest

private theorem completed_not_more {α : Type} (contract : Spec.ParseResult α → Prop) :
    ¬Spec.completed contract .NeedMore := by
  rintro ⟨parsed, _hparsed, heq⟩
  cases parsed with
  | Err error => cases heq
  | Ok pair => cases pair; cases heq

theorem restrict_match_final_spec {P Q α β : Type} (pi : DirectParser P α) (qi : DirectParser Q β)
    (p : P) (q : Q) (input : Slice U8) (cursor : Cursor) (allowEqual : Bool)
    (first : Cursor → Spec.ParseResult α → Prop) (second : Cursor → Spec.ParseResult β → Prop)
    (hp : pi.parse_with p input cursor ParseContext.FINAL ⦃ result => Spec.completed (first cursor) result ⦄)
    (hq : qi.parse_with q input cursor ParseContext.FINAL ⦃ result => Spec.completed (second cursor) result ⦄) :
    DirectRun.restrict_match pi qi p q input cursor ParseContext.FINAL allowEqual
      ⦃ result => Spec.completed (Spec.matchRestriction allowEqual first second cursor) result ⦄ := by
  step with restrict_match_with_spec pi qi p q input cursor ParseContext.FINAL allowEqual
    (fun start => Spec.completed (first start)) (fun start => Spec.completed (second start)) hp hq
    as ⟨result, hresult⟩
  cases result with
  | Success next value => exact ⟨.Ok (next, value), hresult, rfl⟩
  | Error error => exact ⟨.Err error, hresult, rfl⟩
  | NeedMore => exact False.elim (match_restriction_not_more allowEqual _ _ cursor
      (completed_not_more _) (completed_not_more _) hresult)

theorem xor_final_spec {P Q α : Type} (pi : DirectParser P α) (qi : DirectParser Q α)
    (parser : Xor P Q) (input : Slice U8) (cursor : Cursor)
    (first second : Cursor → Spec.ParseResult α → Prop)
    (hp : pi.parse_with parser.first input cursor ParseContext.FINAL ⦃ result => Spec.completed (first cursor) result ⦄)
    (hq : qi.parse_with parser.second input cursor ParseContext.FINAL ⦃ result => Spec.completed (second cursor) result ⦄) :
    Xor.Insts.RusthammerParser.parse_with pi qi parser input cursor ParseContext.FINAL
      ⦃ result => Spec.completed (Spec.exclusive first second cursor) result ⦄ := by
  step with xor_with_spec pi qi parser input cursor ParseContext.FINAL
    (fun start => Spec.completed (first start)) (fun start => Spec.completed (second start)) hp hq
    as ⟨result, hresult⟩
  cases result with
  | Success next value => exact ⟨.Ok (next, value), hresult, rfl⟩
  | Error error => exact ⟨.Err error, hresult, rfl⟩
  | NeedMore => exact False.elim (xor_not_more _ _ cursor (completed_not_more _) (completed_not_more _) hresult)

theorem but_not_final_spec {P Q α β : Type} (pi : DirectParser P α) (qi : DirectParser Q β)
    (parser : ButNot P Q) (input : Slice U8) (cursor : Cursor)
    (first : Cursor → Spec.ParseResult α → Prop) (second : Cursor → Spec.ParseResult β → Prop)
    (hp : pi.parse_with parser.first input cursor ParseContext.FINAL ⦃ result => Spec.completed (first cursor) result ⦄)
    (hq : qi.parse_with parser.second input cursor ParseContext.FINAL ⦃ result => Spec.completed (second cursor) result ⦄) :
    ButNot.Insts.RusthammerParser.parse_with pi qi parser input cursor ParseContext.FINAL
      ⦃ result => Spec.completed (Spec.matchRestriction false first second cursor) result ⦄ := by
  exact restrict_match_final_spec pi qi parser.first parser.second input cursor false first second hp hq

theorem difference_final_spec {P Q α β : Type} (pi : DirectParser P α) (qi : DirectParser Q β)
    (parser : Difference P Q) (input : Slice U8) (cursor : Cursor)
    (first : Cursor → Spec.ParseResult α → Prop) (second : Cursor → Spec.ParseResult β → Prop)
    (hp : pi.parse_with parser.first input cursor ParseContext.FINAL ⦃ result => Spec.completed (first cursor) result ⦄)
    (hq : qi.parse_with parser.second input cursor ParseContext.FINAL ⦃ result => Spec.completed (second cursor) result ⦄) :
    Difference.Insts.RusthammerParser.parse_with pi qi parser input cursor ParseContext.FINAL
      ⦃ result => Spec.completed (Spec.matchRestriction true first second cursor) result ⦄ := by
  exact restrict_match_final_spec pi qi parser.first parser.second input cursor true first second hp hq

theorem but_not_spec {P Q α β : Type} (pi : DirectParser P α) (qi : DirectParser Q β)
    (parser : ButNot P Q) (input : Slice U8) (cursor : Cursor)
    (first : Cursor → Spec.ParseResult α → Prop) (second : Cursor → Spec.ParseResult β → Prop)
    (hp : pi.parse_with parser.first input cursor ParseContext.FINAL ⦃ result => Spec.completed (first cursor) result ⦄)
    (hq : qi.parse_with parser.second input cursor ParseContext.FINAL ⦃ result => Spec.completed (second cursor) result ⦄) :
    DirectParser.parse (ButNot.Insts.RusthammerParser pi qi) parser input cursor
      ⦃ result => Spec.matchRestriction false first second cursor result ⦄ := by
  exact complete_spec _ parser input cursor _ (but_not_final_spec pi qi parser input cursor first second hp hq)

theorem difference_spec {P Q α β : Type} (pi : DirectParser P α) (qi : DirectParser Q β)
    (parser : Difference P Q) (input : Slice U8) (cursor : Cursor)
    (first : Cursor → Spec.ParseResult α → Prop) (second : Cursor → Spec.ParseResult β → Prop)
    (hp : pi.parse_with parser.first input cursor ParseContext.FINAL ⦃ result => Spec.completed (first cursor) result ⦄)
    (hq : qi.parse_with parser.second input cursor ParseContext.FINAL ⦃ result => Spec.completed (second cursor) result ⦄) :
    DirectParser.parse (Difference.Insts.RusthammerParser pi qi) parser input cursor
      ⦃ result => Spec.matchRestriction true first second cursor result ⦄ := by
  exact complete_spec _ parser input cursor _ (difference_final_spec pi qi parser input cursor first second hp hq)

theorem xor_spec {P Q α : Type} (pi : DirectParser P α) (qi : DirectParser Q α)
    (parser : Xor P Q) (input : Slice U8) (cursor : Cursor)
    (first second : Cursor → Spec.ParseResult α → Prop)
    (hp : pi.parse_with parser.first input cursor ParseContext.FINAL ⦃ result => Spec.completed (first cursor) result ⦄)
    (hq : qi.parse_with parser.second input cursor ParseContext.FINAL ⦃ result => Spec.completed (second cursor) result ⦄) :
    DirectParser.parse (Xor.Insts.RusthammerParser pi qi) parser input cursor
      ⦃ result => Spec.exclusive first second cursor result ⦄ := by
  exact complete_spec _ parser input cursor _ (xor_final_spec pi qi parser input cursor first second hp hq)

/-- Restriction preserves the first output and endpoint. Its second match either
rejects recoverably or satisfies the selected consumed-length relation. -/
theorem match_restriction_success {α β : Type} (allowEqual : Bool)
    (first : Cursor → ParseOutcome α → Prop) (second : Cursor → ParseOutcome β → Prop)
    (cursor next : Cursor) (value : α)
    (h : Partial.matchRestriction allowEqual first second cursor (.Success next value)) :
    first cursor (.Success next value) ∧
      ((∃ error, Spec.recoverable error ∧ second cursor (.Error error)) ∨
       ∃ other otherValue, second cursor (.Success other otherValue) ∧
         Spec.matchEndpointOrder allowEqual next other) := by
  rcases h with ⟨left, hleft, hrest⟩
  cases left with
  | NeedMore => cases hrest
  | Error error => cases hrest
  | Success after output =>
    rcases hrest with ⟨right, hright, hrest⟩
    cases right with
    | NeedMore => cases hrest
    | Error error =>
      dsimp only at hrest
      split at hrest
      · cases hrest; exact ⟨hleft, Or.inl ⟨error, by assumption, hright⟩⟩
      · cases hrest
    | Success other otherValue =>
      dsimp only at hrest
      split at hrest
      · cases hrest; exact ⟨hleft, Or.inr ⟨other, otherValue, hright, by assumption⟩⟩
      · cases hrest

/-- A successful exclusive match preserves one child's output and endpoint,
with a recoverable rejection from the other child at the same start. -/
theorem xor_success {α : Type} (first second : Cursor → ParseOutcome α → Prop)
    (cursor next : Cursor) (value : α)
    (h : Partial.exclusive first second cursor (.Success next value)) :
    (first cursor (.Success next value) ∧
      ∃ error, Spec.recoverable error ∧ second cursor (.Error error)) ∨
    (second cursor (.Success next value) ∧
      ∃ error, Spec.recoverable error ∧ first cursor (.Error error)) := by
  rcases h with ⟨left, hleft, hrest⟩
  cases left with
  | NeedMore => cases hrest
  | Error error =>
    dsimp only at hrest
    split at hrest
    · exact Or.inr ⟨hrest, error, by assumption, hleft⟩
    · cases hrest
  | Success after output =>
    rcases hrest with ⟨right, hright, hrest⟩
    cases right with
    | NeedMore => cases hrest
    | Success other otherValue => cases hrest
    | Error error =>
      dsimp only at hrest
      split at hrest
      · cases hrest; exact Or.inl ⟨hleft, error, by assumption, hright⟩
      · cases hrest

-- These laws deliberately make no termination or contract assumption about the
-- second child: short-circuiting must not require that child to run successfully.
theorem restrict_match_first_error {P Q α β : Type} (pi : DirectParser P α) (qi : DirectParser Q β)
    (p : P) (q : Q) (input : Slice U8) (cursor : Cursor) (context : ParseContext)
    (allowEqual : Bool) (error : ParseError)
    (hp : pi.parse_with p input cursor context ⦃ result => result = .Error error ⦄) :
    DirectRun.restrict_match pi qi p q input cursor context allowEqual ⦃ result => result = .Error error ⦄ := by
  rw [DirectRun.restrict_match_eq]
  step with hp as ⟨result, hresult⟩
  subst result
  simp only [spec_ok]

theorem restrict_match_first_more {P Q α β : Type} (pi : DirectParser P α) (qi : DirectParser Q β)
    (p : P) (q : Q) (input : Slice U8) (cursor : Cursor) (context : ParseContext) (allowEqual : Bool)
    (hp : pi.parse_with p input cursor context ⦃ result => result = .NeedMore ⦄) :
    DirectRun.restrict_match pi qi p q input cursor context allowEqual ⦃ result => result = .NeedMore ⦄ := by
  rw [DirectRun.restrict_match_eq]
  step with hp as ⟨result, hresult⟩
  subst result
  simp only [spec_ok]

theorem xor_first_fatal {P Q α : Type} (pi : DirectParser P α) (qi : DirectParser Q α)
    (parser : Xor P Q) (input : Slice U8) (cursor : Cursor) (context : ParseContext) (error : ParseError)
    (hfatal : ¬Spec.recoverable error)
    (hp : pi.parse_with parser.first input cursor context ⦃ result => result = .Error error ⦄) :
    Xor.Insts.RusthammerParser.parse_with pi qi parser input cursor context
      ⦃ result => result = .Error error ⦄ := by
  rw [Xor.Insts.RusthammerParser.parse_with_eq]
  step with hp as ⟨result, hresult⟩
  subst result
  step with recoverable_spec error as ⟨recover, hrecover⟩
  have heq : recover = false := by simpa [hfatal] using hrecover
  simp only [heq, Bool.false_eq_true, ↓reduceIte, spec_ok]

theorem xor_first_more {P Q α : Type} (pi : DirectParser P α) (qi : DirectParser Q α)
    (parser : Xor P Q) (input : Slice U8) (cursor : Cursor) (context : ParseContext)
    (hp : pi.parse_with parser.first input cursor context ⦃ result => result = .NeedMore ⦄) :
    Xor.Insts.RusthammerParser.parse_with pi qi parser input cursor context
      ⦃ result => result = .NeedMore ⦄ := by
  rw [Xor.Insts.RusthammerParser.parse_with_eq]
  step with hp as ⟨result, hresult⟩
  subst result
  simp only [spec_ok]

end RustHammer.Proofs
