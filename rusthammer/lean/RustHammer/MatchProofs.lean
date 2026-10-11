import RustHammer.MatchSpec
import RustHammer.ParserProofs

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

/-- Seeking may return before the common start. Endpoint order still compares
signed net displacements, without a forward-motion premise or unsigned wrap. -/
theorem match_endpoint_order_displacement (allowEqual : Bool) (cursor first second : Cursor)
    (hf : first.bit.val < 8) (hs : second.bit.val < 8) :
    Spec.matchEndpointOrder allowEqual first second ↔
      if allowEqual then
        (Spec.position second : Int) - Spec.position cursor ≤
          (Spec.position first : Int) - Spec.position cursor
      else
        (Spec.position second : Int) - Spec.position cursor <
          (Spec.position first : Int) - Spec.position cursor := by
  rw [match_endpoint_order_bits allowEqual first second hf hs]
  cases allowEqual <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

theorem restrict_match_with_spec {P Q α β : Type} (pi : parser_traits.Parser P α) (qi : parser_traits.Parser Q β)
    (p : P) (q : Q) (input : Slice U8) (cursor : Cursor) (context : ByteOrder) (allowEqual : Bool)
    (first : Cursor → Spec.ParseResult α → Prop) (second : Cursor → Spec.ParseResult β → Prop)
    (hp : pi.parse_with p input cursor context ⦃ result => first cursor result ⦄)
    (hq : qi.parse_with q input cursor context ⦃ result => second cursor result ⦄) :
    grammar.control.restrict_match pi qi p q input cursor context allowEqual
      ⦃ result => Contracts.matchRestriction allowEqual first second cursor result ⦄ := by
  rw [grammar.control.restrict_match]
  step with hp as ⟨left, hleft⟩
  cases left with
  | Err error => simp only [spec_ok]; exact ⟨.Err error, hleft, rfl⟩
  | Ok pair =>
    rcases pair with ⟨next, value⟩
    step with hq as ⟨right, hright⟩
    cases right with
    | Err error =>
      step with recoverable_spec error as ⟨recover, hrecover⟩
      by_cases hr : Spec.recoverable error
      · have heq : recover = true := by simpa [hr] using hrecover
        simp only [heq, ↓reduceIte, spec_ok]
        exact ⟨.Ok (next, value), hleft, .Err error, hright, by simp [hr]⟩
      · have heq : recover = false := by simpa [hr] using hrecover
        simp only [heq, Bool.false_eq_true, ↓reduceIte, spec_ok]
        exact ⟨.Ok (next, value), hleft, .Err error, hright, by simp [hr]⟩
    | Ok pair =>
      rcases pair with ⟨other, otherValue⟩
      step with match_length_allows_spec next other allowEqual as ⟨accepts, haccepts⟩
      by_cases hl : Spec.matchEndpointOrder allowEqual next other
      · have heq : accepts = true := by simpa [hl] using haccepts
        simp only [heq, ↓reduceIte, spec_ok]
        exact ⟨.Ok (next, value), hleft, .Ok (other, otherValue), hright, by simp [hl]⟩
      · have heq : accepts = false := by simpa [hl] using haccepts
        simp only [heq, Bool.false_eq_true, ↓reduceIte, spec_ok]
        exact ⟨.Ok (next, value), hleft, .Ok (other, otherValue), hright, by simp [hl]⟩

theorem but_not_with_spec {P Q α β : Type} (pi : parser_traits.Parser P α) (qi : parser_traits.Parser Q β)
    (parser : ButNot P Q) (input : Slice U8) (cursor : Cursor) (context : ByteOrder)
    (first : Cursor → Spec.ParseResult α → Prop) (second : Cursor → Spec.ParseResult β → Prop)
    (hp : pi.parse_with parser.first input cursor context ⦃ result => first cursor result ⦄)
    (hq : qi.parse_with parser.second input cursor context ⦃ result => second cursor result ⦄) :
    ButNot.Insts.RusthammerParser_traitsParser.parse_with pi qi parser input cursor context
      ⦃ result => Contracts.matchRestriction false first second cursor result ⦄ := by
  exact restrict_match_with_spec pi qi parser.first parser.second input cursor context false first second hp hq

theorem difference_with_spec {P Q α β : Type} (pi : parser_traits.Parser P α) (qi : parser_traits.Parser Q β)
    (parser : Difference P Q) (input : Slice U8) (cursor : Cursor) (context : ByteOrder)
    (first : Cursor → Spec.ParseResult α → Prop) (second : Cursor → Spec.ParseResult β → Prop)
    (hp : pi.parse_with parser.first input cursor context ⦃ result => first cursor result ⦄)
    (hq : qi.parse_with parser.second input cursor context ⦃ result => second cursor result ⦄) :
    Difference.Insts.RusthammerParser_traitsParser.parse_with pi qi parser input cursor context
      ⦃ result => Contracts.matchRestriction true first second cursor result ⦄ := by
  exact restrict_match_with_spec pi qi parser.first parser.second input cursor context true first second hp hq

theorem xor_with_spec {P Q α : Type} (pi : parser_traits.Parser P α) (qi : parser_traits.Parser Q α)
    (parser : Xor P Q) (input : Slice U8) (cursor : Cursor) (context : ByteOrder)
    (first second : Cursor → Spec.ParseResult α → Prop)
    (hp : pi.parse_with parser.first input cursor context ⦃ result => first cursor result ⦄)
    (hq : qi.parse_with parser.second input cursor context ⦃ result => second cursor result ⦄) :
    Xor.Insts.RusthammerParser_traitsParser.parse_with pi qi parser input cursor context
      ⦃ result => Contracts.exclusive first second cursor result ⦄ := by
  rw [Xor.Insts.RusthammerParser_traitsParser.parse_with]
  step with hp as ⟨left, hleft⟩
  cases left with
  | Err error =>
    step with recoverable_spec error as ⟨recover, hrecover⟩
    by_cases hr : Spec.recoverable error
    · have heq : recover = true := by simpa [hr] using hrecover
      simp only [heq, ↓reduceIte]
      step with hq as ⟨right, hright⟩
      exact ⟨.Err error, hleft, by simpa [hr] using hright⟩
    · have heq : recover = false := by simpa [hr] using hrecover
      simp only [heq, Bool.false_eq_true, ↓reduceIte, spec_ok]
      exact ⟨.Err error, hleft, by simp [hr]⟩
  | Ok pair =>
    rcases pair with ⟨next, value⟩
    step with hq as ⟨right, hright⟩
    cases right with
    | Ok pair =>
      rcases pair with ⟨other, otherValue⟩
      simp only [spec_ok]
      exact ⟨.Ok (next, value), hleft, .Ok (other, otherValue), hright, rfl⟩
    | Err error =>
      step with recoverable_spec error as ⟨recover, hrecover⟩
      by_cases hr : Spec.recoverable error
      · have heq : recover = true := by simpa [hr] using hrecover
        simp only [heq, ↓reduceIte, spec_ok]
        exact ⟨.Ok (next, value), hleft, .Err error, hright, by simp [hr]⟩
      · have heq : recover = false := by simpa [hr] using hrecover
        simp only [heq, Bool.false_eq_true, ↓reduceIte, spec_ok]
        exact ⟨.Ok (next, value), hleft, .Err error, hright, by simp [hr]⟩

theorem restrict_match_final_spec {P Q α β : Type} (pi : parser_traits.Parser P α) (qi : parser_traits.Parser Q β)
    (p : P) (q : Q) (input : Slice U8) (cursor : Cursor) (allowEqual : Bool)
    (first : Cursor → Spec.ParseResult α → Prop) (second : Cursor → Spec.ParseResult β → Prop)
    (hp : pi.parse_with p input cursor ByteOrder.Big ⦃ result => Spec.satisfies (first cursor) result ⦄)
    (hq : qi.parse_with q input cursor ByteOrder.Big ⦃ result => Spec.satisfies (second cursor) result ⦄) :
    grammar.control.restrict_match pi qi p q input cursor ByteOrder.Big allowEqual
      ⦃ result => Spec.satisfies (Spec.matchRestriction allowEqual first second cursor) result ⦄ := by
  step with restrict_match_with_spec pi qi p q input cursor ByteOrder.Big allowEqual
    (fun start => Spec.satisfies (first start)) (fun start => Spec.satisfies (second start)) hp hq
    as ⟨result, hresult⟩
  cases result with
  | Ok pair =>
    rcases pair with ⟨next, value⟩
    exact ⟨.Ok (next, value), hresult, rfl⟩
  | Err error => exact ⟨.Err error, hresult, rfl⟩
theorem xor_final_spec {P Q α : Type} (pi : parser_traits.Parser P α) (qi : parser_traits.Parser Q α)
    (parser : Xor P Q) (input : Slice U8) (cursor : Cursor)
    (first second : Cursor → Spec.ParseResult α → Prop)
    (hp : pi.parse_with parser.first input cursor ByteOrder.Big ⦃ result => Spec.satisfies (first cursor) result ⦄)
    (hq : qi.parse_with parser.second input cursor ByteOrder.Big ⦃ result => Spec.satisfies (second cursor) result ⦄) :
    Xor.Insts.RusthammerParser_traitsParser.parse_with pi qi parser input cursor ByteOrder.Big
      ⦃ result => Spec.satisfies (Spec.exclusive first second cursor) result ⦄ := by
  step with xor_with_spec pi qi parser input cursor ByteOrder.Big
    (fun start => Spec.satisfies (first start)) (fun start => Spec.satisfies (second start)) hp hq
    as ⟨result, hresult⟩
  cases result with
  | Ok pair =>
    rcases pair with ⟨next, value⟩
    exact ⟨.Ok (next, value), hresult, rfl⟩
  | Err error => exact ⟨.Err error, hresult, rfl⟩
theorem but_not_final_spec {P Q α β : Type} (pi : parser_traits.Parser P α) (qi : parser_traits.Parser Q β)
    (parser : ButNot P Q) (input : Slice U8) (cursor : Cursor)
    (first : Cursor → Spec.ParseResult α → Prop) (second : Cursor → Spec.ParseResult β → Prop)
    (hp : pi.parse_with parser.first input cursor ByteOrder.Big ⦃ result => Spec.satisfies (first cursor) result ⦄)
    (hq : qi.parse_with parser.second input cursor ByteOrder.Big ⦃ result => Spec.satisfies (second cursor) result ⦄) :
    ButNot.Insts.RusthammerParser_traitsParser.parse_with pi qi parser input cursor ByteOrder.Big
      ⦃ result => Spec.satisfies (Spec.matchRestriction false first second cursor) result ⦄ := by
  exact restrict_match_final_spec pi qi parser.first parser.second input cursor false first second hp hq

theorem difference_final_spec {P Q α β : Type} (pi : parser_traits.Parser P α) (qi : parser_traits.Parser Q β)
    (parser : Difference P Q) (input : Slice U8) (cursor : Cursor)
    (first : Cursor → Spec.ParseResult α → Prop) (second : Cursor → Spec.ParseResult β → Prop)
    (hp : pi.parse_with parser.first input cursor ByteOrder.Big ⦃ result => Spec.satisfies (first cursor) result ⦄)
    (hq : qi.parse_with parser.second input cursor ByteOrder.Big ⦃ result => Spec.satisfies (second cursor) result ⦄) :
    Difference.Insts.RusthammerParser_traitsParser.parse_with pi qi parser input cursor ByteOrder.Big
      ⦃ result => Spec.satisfies (Spec.matchRestriction true first second cursor) result ⦄ := by
  exact restrict_match_final_spec pi qi parser.first parser.second input cursor true first second hp hq

theorem but_not_spec {P Q α β : Type} (pi : parser_traits.Parser P α) (qi : parser_traits.Parser Q β)
    (parser : ButNot P Q) (input : Slice U8) (cursor : Cursor)
    (first : Cursor → Spec.ParseResult α → Prop) (second : Cursor → Spec.ParseResult β → Prop)
    (hp : pi.parse_with parser.first input cursor ByteOrder.Big ⦃ result => Spec.satisfies (first cursor) result ⦄)
    (hq : qi.parse_with parser.second input cursor ByteOrder.Big ⦃ result => Spec.satisfies (second cursor) result ⦄) :
    parser_traits.Parser.parse.default (ButNot.Insts.RusthammerParser_traitsParser pi qi) parser input cursor
      ⦃ result => Spec.matchRestriction false first second cursor result ⦄ := by
  exact complete_spec _ parser input cursor _ (but_not_final_spec pi qi parser input cursor first second hp hq)

theorem difference_spec {P Q α β : Type} (pi : parser_traits.Parser P α) (qi : parser_traits.Parser Q β)
    (parser : Difference P Q) (input : Slice U8) (cursor : Cursor)
    (first : Cursor → Spec.ParseResult α → Prop) (second : Cursor → Spec.ParseResult β → Prop)
    (hp : pi.parse_with parser.first input cursor ByteOrder.Big ⦃ result => Spec.satisfies (first cursor) result ⦄)
    (hq : qi.parse_with parser.second input cursor ByteOrder.Big ⦃ result => Spec.satisfies (second cursor) result ⦄) :
    parser_traits.Parser.parse.default (Difference.Insts.RusthammerParser_traitsParser pi qi) parser input cursor
      ⦃ result => Spec.matchRestriction true first second cursor result ⦄ := by
  exact complete_spec _ parser input cursor _ (difference_final_spec pi qi parser input cursor first second hp hq)

theorem xor_spec {P Q α : Type} (pi : parser_traits.Parser P α) (qi : parser_traits.Parser Q α)
    (parser : Xor P Q) (input : Slice U8) (cursor : Cursor)
    (first second : Cursor → Spec.ParseResult α → Prop)
    (hp : pi.parse_with parser.first input cursor ByteOrder.Big ⦃ result => Spec.satisfies (first cursor) result ⦄)
    (hq : qi.parse_with parser.second input cursor ByteOrder.Big ⦃ result => Spec.satisfies (second cursor) result ⦄) :
    parser_traits.Parser.parse.default (Xor.Insts.RusthammerParser_traitsParser pi qi) parser input cursor
      ⦃ result => Spec.exclusive first second cursor result ⦄ := by
  exact complete_spec _ parser input cursor _ (xor_final_spec pi qi parser input cursor first second hp hq)

/-- Restriction preserves the first output and endpoint. Its second match either
rejects recoverably or satisfies the selected consumed-length relation. -/
theorem match_restriction_success {α β : Type} (allowEqual : Bool)
    (first : Cursor → Spec.ParseResult α → Prop) (second : Cursor → Spec.ParseResult β → Prop)
    (cursor next : Cursor) (value : α)
    (h : Contracts.matchRestriction allowEqual first second cursor (.Ok (next, value))) :
    first cursor (.Ok (next, value)) ∧
      ((∃ error, Spec.recoverable error ∧ second cursor (.Err error)) ∨
       ∃ other otherValue, second cursor (.Ok (other, otherValue)) ∧
         Spec.matchEndpointOrder allowEqual next other) := by
  rcases h with ⟨left, hleft, hrest⟩
  cases left with
  | Err error => cases hrest
  | Ok pair =>
    rcases pair with ⟨after, output⟩
    rcases hrest with ⟨right, hright, hrest⟩
    cases right with
    | Err error =>
      dsimp only at hrest
      split at hrest
      · cases hrest; exact ⟨hleft, Or.inl ⟨error, by assumption, hright⟩⟩
      · cases hrest
    | Ok pair =>
      rcases pair with ⟨other, otherValue⟩
      dsimp only at hrest
      split at hrest
      · cases hrest; exact ⟨hleft, Or.inr ⟨other, otherValue, hright, by assumption⟩⟩
      · cases hrest

/-- A successful exclusive match preserves one child's output and endpoint,
with a recoverable rejection from the other child at the same start. -/
theorem xor_success {α : Type} (first second : Cursor → Spec.ParseResult α → Prop)
    (cursor next : Cursor) (value : α)
    (h : Contracts.exclusive first second cursor (.Ok (next, value))) :
    (first cursor (.Ok (next, value)) ∧
      ∃ error, Spec.recoverable error ∧ second cursor (.Err error)) ∨
    (second cursor (.Ok (next, value)) ∧
      ∃ error, Spec.recoverable error ∧ first cursor (.Err error)) := by
  rcases h with ⟨left, hleft, hrest⟩
  cases left with
  | Err error =>
    dsimp only at hrest
    split at hrest
    · exact Or.inr ⟨hrest, error, by assumption, hleft⟩
    · cases hrest
  | Ok pair =>
    rcases pair with ⟨after, output⟩
    rcases hrest with ⟨right, hright, hrest⟩
    cases right with
    | Ok pair =>
      rcases pair with ⟨other, otherValue⟩
      cases hrest
    | Err error =>
      dsimp only at hrest
      split at hrest
      · cases hrest; exact Or.inl ⟨hleft, error, by assumption, hright⟩
      · cases hrest

-- These laws deliberately make no termination or contract assumption about the
-- second child: short-circuiting must not require that child to run successfully.
theorem restrict_match_first_error {P Q α β : Type} (pi : parser_traits.Parser P α) (qi : parser_traits.Parser Q β)
    (p : P) (q : Q) (input : Slice U8) (cursor : Cursor) (context : ByteOrder)
    (allowEqual : Bool) (error : ParseError)
    (hp : pi.parse_with p input cursor context ⦃ result => result = .Err error ⦄) :
    grammar.control.restrict_match pi qi p q input cursor context allowEqual ⦃ result => result = .Err error ⦄ := by
  rw [grammar.control.restrict_match]
  step with hp as ⟨result, hresult⟩
  subst result
  simp only [spec_ok]

theorem xor_first_fatal {P Q α : Type} (pi : parser_traits.Parser P α) (qi : parser_traits.Parser Q α)
    (parser : Xor P Q) (input : Slice U8) (cursor : Cursor) (context : ByteOrder) (error : ParseError)
    (hfatal : ¬Spec.recoverable error)
    (hp : pi.parse_with parser.first input cursor context ⦃ result => result = .Err error ⦄) :
    Xor.Insts.RusthammerParser_traitsParser.parse_with pi qi parser input cursor context
      ⦃ result => result = .Err error ⦄ := by
  rw [Xor.Insts.RusthammerParser_traitsParser.parse_with]
  step with hp as ⟨result, hresult⟩
  subst result
  step with recoverable_spec error as ⟨recover, hrecover⟩
  have heq : recover = false := by simpa [hfatal] using hrecover
  simp only [heq, Bool.false_eq_true, ↓reduceIte, spec_ok]

end RustHammer.Proofs
