import RustHammer.SelectionSpec
import RustHammer.PartialProofs

open RustHammer.Code.grammar.sequence
  RustHammer.Code.input_types

open Aeneas Aeneas.Std Result WP

namespace RustHammer.Proofs
open Code

/-- Shared references forward evaluation and preserve arbitrary contracts for
both direct convenience entry points. -/
theorem parser_ref_with_spec {P α : Type} (pi : DirectParser P α) (parser : P)
    (input : Slice U8) (cursor : Cursor) (context : ParseContext)
    (contract : ParseOutcome α → Prop)
    (hp : pi.parse_with parser input cursor context ⦃ result => contract result ⦄) :
    Shared0P.Insts.RusthammerParser.parse_with pi parser input cursor context
      ⦃ result => contract result ⦄ := hp

theorem parser_ref_spec {P α : Type} (pi : DirectParser P α) (parser : P)
    (input : Slice U8) (cursor : Cursor) (contract : Spec.ParseResult α → Prop)
    (hp : pi.parse parser input cursor ⦃ result => contract result ⦄) :
    Shared0P.Insts.RusthammerParser.parse pi parser input cursor
      ⦃ result => contract result ⦄ := hp

theorem left_with_spec {P Q α β : Type} (pi : DirectParser P α) (qi : DirectParser Q β)
    (parser : Left P Q) (input : Slice U8) (cursor : Cursor) (context : ParseContext)
    (first : Cursor → ParseOutcome α → Prop) (second : Cursor → ParseOutcome β → Prop)
    (hp : ∀ start, pi.parse_with parser.first input start context ⦃ result => first start result ⦄)
    (hq : ∀ start, qi.parse_with parser.second input start context ⦃ result => second start result ⦄) :
    Left.Insts.RusthammerParser.parse_with pi qi parser input cursor context
      ⦃ result => Partial.left first second cursor result ⦄ := by
  rw [Left.Insts.RusthammerParser.parse_with_eq]
  step with seq_with_spec (Shared0P.Insts.RusthammerParser pi) (Shared0P.Insts.RusthammerParser qi)
    { first := parser.first, second := parser.second } input cursor context first second hp hq
    as ⟨parsed, hparsed⟩
  cases parsed with
  | NeedMore => exact ⟨.NeedMore, hparsed, rfl⟩
  | Error error => exact ⟨.Error error, hparsed, rfl⟩
  | Success next pair =>
    rcases pair with ⟨a, b⟩
    exact ⟨.Success next (a, b), hparsed, a, rfl, rfl⟩

theorem left_final_spec {P Q α β : Type} (pi : DirectParser P α) (qi : DirectParser Q β)
    (parser : Left P Q) (input : Slice U8) (cursor : Cursor)
    (first : Cursor → Spec.ParseResult α → Prop) (second : Cursor → Spec.ParseResult β → Prop)
    (hp : ∀ start, pi.parse_with parser.first input start ParseContext.FINAL
      ⦃ result => Spec.completed (first start) result ⦄)
    (hq : ∀ start, qi.parse_with parser.second input start ParseContext.FINAL
      ⦃ result => Spec.completed (second start) result ⦄) :
    Left.Insts.RusthammerParser.parse_with pi qi parser input cursor ParseContext.FINAL
      ⦃ result => Spec.completed (Spec.left first second cursor) result ⦄ := by
  rw [Left.Insts.RusthammerParser.parse_with_eq]
  step with seq_spec (Shared0P.Insts.RusthammerParser pi) (Shared0P.Insts.RusthammerParser qi)
    { first := parser.first, second := parser.second } input cursor first second hp hq
    as ⟨outcome, houtcome⟩
  rcases houtcome with ⟨parsed, hparsed, rfl⟩
  cases parsed with
  | Err error =>
    simp only [Spec.completedResult, spec_ok, Spec.completed_error]
    exact ⟨.Err error, hparsed, rfl⟩
  | Ok pair =>
    rcases pair with ⟨next, a, b⟩
    simp only [Spec.completedResult]
    exact ⟨.Ok (next, a), ⟨.Ok (next, (a, b)), hparsed, a, rfl, rfl⟩, rfl⟩

theorem left_spec {P Q α β : Type} (pi : DirectParser P α) (qi : DirectParser Q β)
    (parser : Left P Q) (input : Slice U8) (cursor : Cursor)
    (first : Cursor → Spec.ParseResult α → Prop) (second : Cursor → Spec.ParseResult β → Prop)
    (hp : ∀ start, pi.parse_with parser.first input start ParseContext.FINAL
      ⦃ result => Spec.completed (first start) result ⦄)
    (hq : ∀ start, qi.parse_with parser.second input start ParseContext.FINAL
      ⦃ result => Spec.completed (second start) result ⦄) :
    DirectParser.parse (Left.Insts.RusthammerParser pi qi) parser input cursor
      ⦃ result => Spec.left first second cursor result ⦄ :=
  complete_spec (Left.Insts.RusthammerParser pi qi) parser input cursor
    (Spec.left first second cursor) (left_final_spec pi qi parser input cursor first second hp hq)

theorem right_with_spec {P Q α β : Type} (pi : DirectParser P α) (qi : DirectParser Q β)
    (parser : Right P Q) (input : Slice U8) (cursor : Cursor) (context : ParseContext)
    (first : Cursor → ParseOutcome α → Prop) (second : Cursor → ParseOutcome β → Prop)
    (hp : ∀ start, pi.parse_with parser.first input start context ⦃ result => first start result ⦄)
    (hq : ∀ start, qi.parse_with parser.second input start context ⦃ result => second start result ⦄) :
    Right.Insts.RusthammerParser.parse_with pi qi parser input cursor context
      ⦃ result => Partial.right first second cursor result ⦄ := by
  rw [Right.Insts.RusthammerParser.parse_with_eq]
  step with seq_with_spec (Shared0P.Insts.RusthammerParser pi) (Shared0P.Insts.RusthammerParser qi)
    { first := parser.first, second := parser.second } input cursor context first second hp hq
    as ⟨parsed, hparsed⟩
  cases parsed with
  | NeedMore => exact ⟨.NeedMore, hparsed, rfl⟩
  | Error error => exact ⟨.Error error, hparsed, rfl⟩
  | Success next pair =>
    rcases pair with ⟨a, b⟩
    exact ⟨.Success next (a, b), hparsed, b, rfl, rfl⟩

theorem right_final_spec {P Q α β : Type} (pi : DirectParser P α) (qi : DirectParser Q β)
    (parser : Right P Q) (input : Slice U8) (cursor : Cursor)
    (first : Cursor → Spec.ParseResult α → Prop) (second : Cursor → Spec.ParseResult β → Prop)
    (hp : ∀ start, pi.parse_with parser.first input start ParseContext.FINAL
      ⦃ result => Spec.completed (first start) result ⦄)
    (hq : ∀ start, qi.parse_with parser.second input start ParseContext.FINAL
      ⦃ result => Spec.completed (second start) result ⦄) :
    Right.Insts.RusthammerParser.parse_with pi qi parser input cursor ParseContext.FINAL
      ⦃ result => Spec.completed (Spec.right first second cursor) result ⦄ := by
  rw [Right.Insts.RusthammerParser.parse_with_eq]
  step with seq_spec (Shared0P.Insts.RusthammerParser pi) (Shared0P.Insts.RusthammerParser qi)
    { first := parser.first, second := parser.second } input cursor first second hp hq
    as ⟨outcome, houtcome⟩
  rcases houtcome with ⟨parsed, hparsed, rfl⟩
  cases parsed with
  | Err error =>
    simp only [Spec.completedResult, spec_ok, Spec.completed_error]
    exact ⟨.Err error, hparsed, rfl⟩
  | Ok pair =>
    rcases pair with ⟨next, a, b⟩
    simp only [Spec.completedResult]
    exact ⟨.Ok (next, b), ⟨.Ok (next, (a, b)), hparsed, b, rfl, rfl⟩, rfl⟩

theorem right_spec {P Q α β : Type} (pi : DirectParser P α) (qi : DirectParser Q β)
    (parser : Right P Q) (input : Slice U8) (cursor : Cursor)
    (first : Cursor → Spec.ParseResult α → Prop) (second : Cursor → Spec.ParseResult β → Prop)
    (hp : ∀ start, pi.parse_with parser.first input start ParseContext.FINAL
      ⦃ result => Spec.completed (first start) result ⦄)
    (hq : ∀ start, qi.parse_with parser.second input start ParseContext.FINAL
      ⦃ result => Spec.completed (second start) result ⦄) :
    DirectParser.parse (Right.Insts.RusthammerParser pi qi) parser input cursor
      ⦃ result => Spec.right first second cursor result ⦄ :=
  complete_spec (Right.Insts.RusthammerParser pi qi) parser input cursor
    (Spec.right first second cursor) (right_final_spec pi qi parser input cursor first second hp hq)

theorem middle_with_spec {L P R α β γ : Type}
    (li : DirectParser L α) (pi : DirectParser P β) (ri : DirectParser R γ) (parser : Middle L P R)
    (input : Slice U8) (cursor : Cursor) (context : ParseContext)
    (before : Cursor → ParseOutcome α → Prop) (child : Cursor → ParseOutcome β → Prop)
    (after : Cursor → ParseOutcome γ → Prop)
    (hl : ∀ start, li.parse_with parser.left input start context ⦃ result => before start result ⦄)
    (hp : ∀ start, pi.parse_with parser.parser input start context ⦃ result => child start result ⦄)
    (hr : ∀ start, ri.parse_with parser.right input start context ⦃ result => after start result ⦄) :
    Middle.Insts.RusthammerParser.parse_with li pi ri parser input cursor context
      ⦃ result => Partial.middle before child after cursor result ⦄ := by
  rw [Middle.Insts.RusthammerParser.parse_with_eq]
  step with seq_with_spec (Shared0P.Insts.RusthammerParser li)
    (Seq.Insts.RusthammerParserInputPair (Shared0P.Insts.RusthammerParser pi)
      (Shared0P.Insts.RusthammerParser ri))
    { first := parser.left, second := { first := parser.parser, second := parser.right } }
    input cursor context before (Partial.sequence child after) hl
    (fun start => seq_with_spec (Shared0P.Insts.RusthammerParser pi)
      (Shared0P.Insts.RusthammerParser ri)
      { first := parser.parser, second := parser.right } input start context child after hp hr)
    as ⟨parsed, hparsed⟩
  cases parsed with
  | NeedMore => exact ⟨.NeedMore, hparsed, rfl⟩
  | Error error => exact ⟨.Error error, hparsed, rfl⟩
  | Success next pair =>
    rcases pair with ⟨a, b, c⟩
    exact ⟨.Success next (a, (b, c)), hparsed, b, rfl, rfl⟩

theorem middle_final_spec {L P R α β γ : Type}
    (li : DirectParser L α) (pi : DirectParser P β) (ri : DirectParser R γ) (parser : Middle L P R)
    (input : Slice U8) (cursor : Cursor)
    (before : Cursor → Spec.ParseResult α → Prop) (child : Cursor → Spec.ParseResult β → Prop)
    (after : Cursor → Spec.ParseResult γ → Prop)
    (hl : ∀ start, li.parse_with parser.left input start ParseContext.FINAL
      ⦃ result => Spec.completed (before start) result ⦄)
    (hp : ∀ start, pi.parse_with parser.parser input start ParseContext.FINAL
      ⦃ result => Spec.completed (child start) result ⦄)
    (hr : ∀ start, ri.parse_with parser.right input start ParseContext.FINAL
      ⦃ result => Spec.completed (after start) result ⦄) :
    Middle.Insts.RusthammerParser.parse_with li pi ri parser input cursor ParseContext.FINAL
      ⦃ result => Spec.completed (Spec.middle before child after cursor) result ⦄ := by
  rw [Middle.Insts.RusthammerParser.parse_with_eq]
  step with seq_spec (Shared0P.Insts.RusthammerParser li)
    (Seq.Insts.RusthammerParserInputPair (Shared0P.Insts.RusthammerParser pi)
      (Shared0P.Insts.RusthammerParser ri))
    { first := parser.left, second := { first := parser.parser, second := parser.right } }
    input cursor before (Spec.sequence child after) hl
    (fun start => seq_spec (Shared0P.Insts.RusthammerParser pi)
      (Shared0P.Insts.RusthammerParser ri)
      { first := parser.parser, second := parser.right } input start child after hp hr)
    as ⟨outcome, houtcome⟩
  rcases houtcome with ⟨parsed, hparsed, rfl⟩
  cases parsed with
  | Err error =>
    simp only [Spec.completedResult, spec_ok, Spec.completed_error]
    exact ⟨.Err error, hparsed, rfl⟩
  | Ok pair =>
    rcases pair with ⟨next, a, b, c⟩
    simp only [Spec.completedResult]
    exact ⟨.Ok (next, b), ⟨.Ok (next, (a, (b, c))), hparsed, b, rfl, rfl⟩, rfl⟩

theorem middle_spec {L P R α β γ : Type}
    (li : DirectParser L α) (pi : DirectParser P β) (ri : DirectParser R γ) (parser : Middle L P R)
    (input : Slice U8) (cursor : Cursor)
    (before : Cursor → Spec.ParseResult α → Prop) (child : Cursor → Spec.ParseResult β → Prop)
    (after : Cursor → Spec.ParseResult γ → Prop)
    (hl : ∀ start, li.parse_with parser.left input start ParseContext.FINAL
      ⦃ result => Spec.completed (before start) result ⦄)
    (hp : ∀ start, pi.parse_with parser.parser input start ParseContext.FINAL
      ⦃ result => Spec.completed (child start) result ⦄)
    (hr : ∀ start, ri.parse_with parser.right input start ParseContext.FINAL
      ⦃ result => Spec.completed (after start) result ⦄) :
    DirectParser.parse (Middle.Insts.RusthammerParser li pi ri) parser input cursor
      ⦃ result => Spec.middle before child after cursor result ⦄ :=
  complete_spec (Middle.Insts.RusthammerParser li pi ri) parser input cursor
    (Spec.middle before child after cursor)
    (middle_final_spec li pi ri parser input cursor before child after hl hp hr)

theorem ignore_with_spec {P α : Type} (pi : DirectParser P α) (parser : Ignore P)
    (input : Slice U8) (cursor : Cursor) (context : ParseContext)
    (child : Cursor → ParseOutcome α → Prop)
    (hp : pi.parse_with parser.parser input cursor context ⦃ result => child cursor result ⦄) :
    Ignore.Insts.RusthammerParserInputTuple.parse_with pi parser input cursor context
      ⦃ result => Partial.ignore child cursor result ⦄ := by
  rw [Ignore.Insts.RusthammerParserInputTuple.parse_with_eq]
  step with hp as ⟨parsed, hparsed⟩
  cases parsed with
  | NeedMore => exact ⟨.NeedMore, hparsed, rfl⟩
  | Error error => exact ⟨.Error error, hparsed, rfl⟩
  | Success next value => exact ⟨.Success next value, hparsed, (), rfl, rfl⟩

theorem ignore_final_spec {P α : Type} (pi : DirectParser P α) (parser : Ignore P)
    (input : Slice U8) (cursor : Cursor) (child : Cursor → Spec.ParseResult α → Prop)
    (hp : pi.parse_with parser.parser input cursor ParseContext.FINAL
      ⦃ result => Spec.completed (child cursor) result ⦄) :
    Ignore.Insts.RusthammerParserInputTuple.parse_with pi parser input cursor ParseContext.FINAL
      ⦃ result => Spec.completed (Spec.ignore child cursor) result ⦄ := by
  rw [Ignore.Insts.RusthammerParserInputTuple.parse_with_eq]
  step with hp as ⟨outcome, houtcome⟩
  rcases houtcome with ⟨parsed, hparsed, rfl⟩
  cases parsed with
  | Err error =>
    simp only [Spec.completedResult, spec_ok, Spec.completed_error]
    exact ⟨.Err error, hparsed, rfl⟩
  | Ok pair =>
    rcases pair with ⟨next, value⟩
    simp only [Spec.completedResult, spec_ok, Spec.completed_success]
    exact ⟨.Ok (next, value), hparsed, (), rfl, rfl⟩

theorem ignore_spec {P α : Type} (pi : DirectParser P α) (parser : Ignore P)
    (input : Slice U8) (cursor : Cursor) (child : Cursor → Spec.ParseResult α → Prop)
    (hp : pi.parse_with parser.parser input cursor ParseContext.FINAL
      ⦃ result => Spec.completed (child cursor) result ⦄) :
    DirectParser.parse (Ignore.Insts.RusthammerParserInputTuple pi) parser input cursor
      ⦃ result => Spec.ignore child cursor result ⦄ :=
  complete_spec (Ignore.Insts.RusthammerParserInputTuple pi) parser input cursor
    (Spec.ignore child cursor) (ignore_final_spec pi parser input cursor child hp)

/-- A successful mapping keeps the child's success cursor. -/
theorem map_success_value {α β : Type} (child : Cursor → ParseOutcome α → Prop)
    (mapping : α → β → Prop) (cursor next : Cursor) (mapped : β)
    (h : Partial.map child mapping cursor (.Success next mapped)) :
    ∃ value, child cursor (.Success next value) ∧ mapping value mapped := by
  rcases h with ⟨parsed, hparsed, hresult⟩
  cases parsed with
  | NeedMore => cases hresult
  | Error _ => cases hresult
  | Success after value =>
    rcases hresult with ⟨result, hmapped, heq⟩
    cases heq
    exact ⟨value, hparsed, hmapped⟩

/-- A successful sequence witnesses both child successes and their shared cursor. -/
theorem sequence_success_children {α β : Type} (first : Cursor → ParseOutcome α → Prop)
    (second : Cursor → ParseOutcome β → Prop) (cursor next : Cursor) (a : α) (b : β)
    (h : Partial.sequence first second cursor (.Success next (a, b))) :
    ∃ middle, first cursor (.Success middle a) ∧ second middle (.Success next b) := by
  rcases h with ⟨left, hleft, hresult⟩
  cases left with
  | NeedMore => cases hresult
  | Error _ => cases hresult
  | Success middle value =>
    rcases hresult with ⟨right, hright, heq⟩
    cases right with
    | NeedMore => cases heq
    | Error _ => cases heq
    | Success after other =>
      cases heq
      exact ⟨middle, hleft, hright⟩

theorem left_success_children {α β : Type} (first : Cursor → ParseOutcome α → Prop)
    (second : Cursor → ParseOutcome β → Prop) (cursor next : Cursor) (value : α)
    (h : Partial.left first second cursor (.Success next value)) :
    ∃ middle other, first cursor (.Success middle value) ∧ second middle (.Success next other) := by
  rcases map_success_value _ _ _ _ _ h with ⟨⟨a, b⟩, hseq, rfl⟩
  obtain ⟨middle, hfirst, hsecond⟩ := sequence_success_children _ _ _ _ value b hseq
  exact ⟨middle, b, hfirst, hsecond⟩

theorem right_success_children {α β : Type} (first : Cursor → ParseOutcome α → Prop)
    (second : Cursor → ParseOutcome β → Prop) (cursor next : Cursor) (value : β)
    (h : Partial.right first second cursor (.Success next value)) :
    ∃ middle other, first cursor (.Success middle other) ∧ second middle (.Success next value) := by
  rcases map_success_value _ _ _ _ _ h with ⟨⟨a, b⟩, hseq, rfl⟩
  obtain ⟨middle, hfirst, hsecond⟩ := sequence_success_children _ _ _ _ a value hseq
  exact ⟨middle, a, hfirst, hsecond⟩

theorem middle_success_children {α β γ : Type} (before : Cursor → ParseOutcome α → Prop)
    (child : Cursor → ParseOutcome β → Prop) (after : Cursor → ParseOutcome γ → Prop)
    (cursor next : Cursor) (value : β)
    (h : Partial.middle before child after cursor (.Success next value)) :
    ∃ first second a c, before cursor (.Success first a) ∧
      child first (.Success second value) ∧ after second (.Success next c) := by
  rcases map_success_value _ _ _ _ _ h with ⟨⟨a, b, c⟩, hseq, rfl⟩
  obtain ⟨first, hbefore, hrest⟩ := sequence_success_children _ _ _ _ a (value, c) hseq
  obtain ⟨second, hchild, hafter⟩ := sequence_success_children _ _ _ _ value c hrest
  exact ⟨first, second, a, c, hbefore, hchild, hafter⟩

theorem ignore_success_cursor {α : Type} (child : Cursor → ParseOutcome α → Prop)
    (cursor next : Cursor) (h : Partial.ignore child cursor (.Success next ())) :
    ∃ value, child cursor (.Success next value) := by
  obtain ⟨value, hchild, _⟩ := map_success_value _ _ _ _ _ h
  exact ⟨value, hchild⟩

end RustHammer.Proofs
