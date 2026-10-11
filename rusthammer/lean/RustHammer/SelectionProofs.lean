import RustHammer.SelectionSpec
import RustHammer.ParserProofs

open RustHammer.Code.grammar.sequence
  RustHammer.Code.input_types

open Aeneas Aeneas.Std Result WP

namespace RustHammer.Proofs
open Code

/-- Shared references forward evaluation and preserve arbitrary contracts for
both direct convenience entry points. -/
theorem parser_ref_with_spec {P α : Type} (pi : parser_traits.Parser P α) (parser : P)
    (input : Slice U8) (cursor : Cursor) (context : ByteOrder)
    (contract : Spec.ParseResult α → Prop)
    (hp : pi.parse_with parser input cursor context ⦃ result => contract result ⦄) :
    Shared0P.Insts.RusthammerParser_traitsParser.parse_with pi parser input cursor context
      ⦃ result => contract result ⦄ := hp

theorem parser_ref_spec {P α : Type} (pi : parser_traits.Parser P α) (parser : P)
    (input : Slice U8) (cursor : Cursor) (contract : Spec.ParseResult α → Prop)
    (hp : parser_traits.Parser.parse.default pi parser input cursor ⦃ result => contract result ⦄) :
    parser_traits.Parser.parse.default (Shared0P.Insts.RusthammerParser_traitsParser pi) parser input cursor
      ⦃ result => contract result ⦄ := hp

theorem left_with_spec {P Q α β : Type} (pi : parser_traits.Parser P α) (qi : parser_traits.Parser Q β)
    (parser : Left P Q) (input : Slice U8) (cursor : Cursor) (context : ByteOrder)
    (first : Cursor → Spec.ParseResult α → Prop) (second : Cursor → Spec.ParseResult β → Prop)
    (hp : ∀ start, pi.parse_with parser.first input start context ⦃ result => first start result ⦄)
    (hq : ∀ start, qi.parse_with parser.second input start context ⦃ result => second start result ⦄) :
    Left.Insts.RusthammerParser_traitsParser.parse_with pi qi parser input cursor context
      ⦃ result => Spec.left first second cursor result ⦄ := by
  rw [Left.Insts.RusthammerParser_traitsParser.parse_with]
  step with seq_with_spec (Shared0P.Insts.RusthammerParser_traitsParser pi) (Shared0P.Insts.RusthammerParser_traitsParser qi)
    { first := parser.first, second := parser.second } input cursor context first second hp hq
    as ⟨parsed, hparsed⟩
  cases parsed with
  | Err error => exact ⟨.Err error, hparsed, rfl⟩
  | Ok pair =>
    rcases pair with ⟨next, pair⟩
    rcases pair with ⟨a, b⟩
    exact ⟨.Ok (next, (a, b)), hparsed, a, rfl, rfl⟩

theorem left_final_spec {P Q α β : Type} (pi : parser_traits.Parser P α) (qi : parser_traits.Parser Q β)
    (parser : Left P Q) (input : Slice U8) (cursor : Cursor)
    (first : Cursor → Spec.ParseResult α → Prop) (second : Cursor → Spec.ParseResult β → Prop)
    (hp : ∀ start, pi.parse_with parser.first input start ByteOrder.Big
      ⦃ result => first start result ⦄)
    (hq : ∀ start, qi.parse_with parser.second input start ByteOrder.Big
      ⦃ result => second start result ⦄) :
    Left.Insts.RusthammerParser_traitsParser.parse_with pi qi parser input cursor ByteOrder.Big
      ⦃ result => Spec.left first second cursor result ⦄ := by
  exact left_with_spec pi qi parser input cursor ByteOrder.Big first second hp hq

theorem left_spec {P Q α β : Type} (pi : parser_traits.Parser P α) (qi : parser_traits.Parser Q β)
    (parser : Left P Q) (input : Slice U8) (cursor : Cursor)
    (first : Cursor → Spec.ParseResult α → Prop) (second : Cursor → Spec.ParseResult β → Prop)
    (hp : ∀ start, pi.parse_with parser.first input start ByteOrder.Big
      ⦃ result => first start result ⦄)
    (hq : ∀ start, qi.parse_with parser.second input start ByteOrder.Big
      ⦃ result => second start result ⦄) :
    parser_traits.Parser.parse.default (Left.Insts.RusthammerParser_traitsParser pi qi) parser input cursor
      ⦃ result => Spec.left first second cursor result ⦄ :=
  complete_spec (Left.Insts.RusthammerParser_traitsParser pi qi) parser input cursor
    (Spec.left first second cursor) (left_final_spec pi qi parser input cursor first second hp hq)

theorem right_with_spec {P Q α β : Type} (pi : parser_traits.Parser P α) (qi : parser_traits.Parser Q β)
    (parser : Right P Q) (input : Slice U8) (cursor : Cursor) (context : ByteOrder)
    (first : Cursor → Spec.ParseResult α → Prop) (second : Cursor → Spec.ParseResult β → Prop)
    (hp : ∀ start, pi.parse_with parser.first input start context ⦃ result => first start result ⦄)
    (hq : ∀ start, qi.parse_with parser.second input start context ⦃ result => second start result ⦄) :
    Right.Insts.RusthammerParser_traitsParser.parse_with pi qi parser input cursor context
      ⦃ result => Spec.right first second cursor result ⦄ := by
  rw [Right.Insts.RusthammerParser_traitsParser.parse_with]
  step with seq_with_spec (Shared0P.Insts.RusthammerParser_traitsParser pi) (Shared0P.Insts.RusthammerParser_traitsParser qi)
    { first := parser.first, second := parser.second } input cursor context first second hp hq
    as ⟨parsed, hparsed⟩
  cases parsed with
  | Err error => exact ⟨.Err error, hparsed, rfl⟩
  | Ok pair =>
    rcases pair with ⟨next, pair⟩
    rcases pair with ⟨a, b⟩
    exact ⟨.Ok (next, (a, b)), hparsed, b, rfl, rfl⟩

theorem right_final_spec {P Q α β : Type} (pi : parser_traits.Parser P α) (qi : parser_traits.Parser Q β)
    (parser : Right P Q) (input : Slice U8) (cursor : Cursor)
    (first : Cursor → Spec.ParseResult α → Prop) (second : Cursor → Spec.ParseResult β → Prop)
    (hp : ∀ start, pi.parse_with parser.first input start ByteOrder.Big
      ⦃ result => first start result ⦄)
    (hq : ∀ start, qi.parse_with parser.second input start ByteOrder.Big
      ⦃ result => second start result ⦄) :
    Right.Insts.RusthammerParser_traitsParser.parse_with pi qi parser input cursor ByteOrder.Big
      ⦃ result => Spec.right first second cursor result ⦄ := by
  exact right_with_spec pi qi parser input cursor ByteOrder.Big first second hp hq

theorem right_spec {P Q α β : Type} (pi : parser_traits.Parser P α) (qi : parser_traits.Parser Q β)
    (parser : Right P Q) (input : Slice U8) (cursor : Cursor)
    (first : Cursor → Spec.ParseResult α → Prop) (second : Cursor → Spec.ParseResult β → Prop)
    (hp : ∀ start, pi.parse_with parser.first input start ByteOrder.Big
      ⦃ result => first start result ⦄)
    (hq : ∀ start, qi.parse_with parser.second input start ByteOrder.Big
      ⦃ result => second start result ⦄) :
    parser_traits.Parser.parse.default (Right.Insts.RusthammerParser_traitsParser pi qi) parser input cursor
      ⦃ result => Spec.right first second cursor result ⦄ :=
  complete_spec (Right.Insts.RusthammerParser_traitsParser pi qi) parser input cursor
    (Spec.right first second cursor) (right_final_spec pi qi parser input cursor first second hp hq)

theorem middle_with_spec {L P R α β γ : Type}
    (li : parser_traits.Parser L α) (pi : parser_traits.Parser P β) (ri : parser_traits.Parser R γ) (parser : Middle L P R)
    (input : Slice U8) (cursor : Cursor) (context : ByteOrder)
    (before : Cursor → Spec.ParseResult α → Prop) (child : Cursor → Spec.ParseResult β → Prop)
    (after : Cursor → Spec.ParseResult γ → Prop)
    (hl : ∀ start, li.parse_with parser.left input start context ⦃ result => before start result ⦄)
    (hp : ∀ start, pi.parse_with parser.parser input start context ⦃ result => child start result ⦄)
    (hr : ∀ start, ri.parse_with parser.right input start context ⦃ result => after start result ⦄) :
    Middle.Insts.RusthammerParser_traitsParser.parse_with li pi ri parser input cursor context
      ⦃ result => Spec.middle before child after cursor result ⦄ := by
  rw [Middle.Insts.RusthammerParser_traitsParser.parse_with]
  step with seq_with_spec (Shared0P.Insts.RusthammerParser_traitsParser li)
    (Seq.Insts.RusthammerParser_traitsParserInputPair (Shared0P.Insts.RusthammerParser_traitsParser pi)
      (Shared0P.Insts.RusthammerParser_traitsParser ri))
    { first := parser.left, second := { first := parser.parser, second := parser.right } }
    input cursor context before (Spec.sequence child after) hl
    (fun start => seq_with_spec (Shared0P.Insts.RusthammerParser_traitsParser pi)
      (Shared0P.Insts.RusthammerParser_traitsParser ri)
      { first := parser.parser, second := parser.right } input start context child after hp hr)
    as ⟨parsed, hparsed⟩
  cases parsed with
  | Err error => exact ⟨.Err error, hparsed, rfl⟩
  | Ok pair =>
    rcases pair with ⟨next, pair⟩
    rcases pair with ⟨a, b, c⟩
    exact ⟨.Ok (next, (a, (b, c))), hparsed, b, rfl, rfl⟩

theorem middle_final_spec {L P R α β γ : Type}
    (li : parser_traits.Parser L α) (pi : parser_traits.Parser P β) (ri : parser_traits.Parser R γ) (parser : Middle L P R)
    (input : Slice U8) (cursor : Cursor)
    (before : Cursor → Spec.ParseResult α → Prop) (child : Cursor → Spec.ParseResult β → Prop)
    (after : Cursor → Spec.ParseResult γ → Prop)
    (hl : ∀ start, li.parse_with parser.left input start ByteOrder.Big
      ⦃ result => before start result ⦄)
    (hp : ∀ start, pi.parse_with parser.parser input start ByteOrder.Big
      ⦃ result => child start result ⦄)
    (hr : ∀ start, ri.parse_with parser.right input start ByteOrder.Big
      ⦃ result => after start result ⦄) :
    Middle.Insts.RusthammerParser_traitsParser.parse_with li pi ri parser input cursor ByteOrder.Big
      ⦃ result => Spec.middle before child after cursor result ⦄ := by
  exact middle_with_spec li pi ri parser input cursor ByteOrder.Big before child after hl hp hr

theorem middle_spec {L P R α β γ : Type}
    (li : parser_traits.Parser L α) (pi : parser_traits.Parser P β) (ri : parser_traits.Parser R γ) (parser : Middle L P R)
    (input : Slice U8) (cursor : Cursor)
    (before : Cursor → Spec.ParseResult α → Prop) (child : Cursor → Spec.ParseResult β → Prop)
    (after : Cursor → Spec.ParseResult γ → Prop)
    (hl : ∀ start, li.parse_with parser.left input start ByteOrder.Big
      ⦃ result => before start result ⦄)
    (hp : ∀ start, pi.parse_with parser.parser input start ByteOrder.Big
      ⦃ result => child start result ⦄)
    (hr : ∀ start, ri.parse_with parser.right input start ByteOrder.Big
      ⦃ result => after start result ⦄) :
    parser_traits.Parser.parse.default (Middle.Insts.RusthammerParser_traitsParser li pi ri) parser input cursor
      ⦃ result => Spec.middle before child after cursor result ⦄ :=
  complete_spec (Middle.Insts.RusthammerParser_traitsParser li pi ri) parser input cursor
    (Spec.middle before child after cursor)
    (middle_final_spec li pi ri parser input cursor before child after hl hp hr)

theorem ignore_with_spec {P α : Type} (pi : parser_traits.Parser P α) (parser : Ignore P)
    (input : Slice U8) (cursor : Cursor) (context : ByteOrder)
    (child : Cursor → Spec.ParseResult α → Prop)
    (hp : pi.parse_with parser.parser input cursor context ⦃ result => child cursor result ⦄) :
    Ignore.Insts.RusthammerParser_traitsParserInputTuple.parse_with pi parser input cursor context
      ⦃ result => Spec.ignore child cursor result ⦄ := by
  rw [Ignore.Insts.RusthammerParser_traitsParserInputTuple.parse_with]
  step with hp as ⟨parsed, hparsed⟩
  cases parsed with
  | Err error => exact ⟨.Err error, hparsed, rfl⟩
  | Ok pair =>
    rcases pair with ⟨next, value⟩
    exact ⟨.Ok (next, value), hparsed, (), rfl, rfl⟩

theorem ignore_final_spec {P α : Type} (pi : parser_traits.Parser P α) (parser : Ignore P)
    (input : Slice U8) (cursor : Cursor) (child : Cursor → Spec.ParseResult α → Prop)
    (hp : pi.parse_with parser.parser input cursor ByteOrder.Big
      ⦃ result => child cursor result ⦄) :
    Ignore.Insts.RusthammerParser_traitsParserInputTuple.parse_with pi parser input cursor ByteOrder.Big
      ⦃ result => Spec.ignore child cursor result ⦄ := by
  exact ignore_with_spec pi parser input cursor ByteOrder.Big child hp

theorem ignore_spec {P α : Type} (pi : parser_traits.Parser P α) (parser : Ignore P)
    (input : Slice U8) (cursor : Cursor) (child : Cursor → Spec.ParseResult α → Prop)
    (hp : pi.parse_with parser.parser input cursor ByteOrder.Big
      ⦃ result => child cursor result ⦄) :
    parser_traits.Parser.parse.default (Ignore.Insts.RusthammerParser_traitsParserInputTuple pi) parser input cursor
      ⦃ result => Spec.ignore child cursor result ⦄ :=
  complete_spec (Ignore.Insts.RusthammerParser_traitsParserInputTuple pi) parser input cursor
    (Spec.ignore child cursor) (ignore_final_spec pi parser input cursor child hp)

/-- A successful mapping keeps the child's success cursor. -/
theorem map_success_value {α β : Type} (child : Cursor → Spec.ParseResult α → Prop)
    (mapping : α → β → Prop) (cursor next : Cursor) (mapped : β)
    (h : Spec.map child mapping cursor (.Ok (next, mapped))) :
    ∃ value, child cursor (.Ok (next, value)) ∧ mapping value mapped := by
  rcases h with ⟨parsed, hparsed, hresult⟩
  cases parsed with
  | Err _ => cases hresult
  | Ok pair =>
    rcases pair with ⟨after, value⟩
    rcases hresult with ⟨result, hmapped, heq⟩
    cases heq
    exact ⟨value, hparsed, hmapped⟩

/-- A successful sequence witnesses both child successes and their shared cursor. -/
theorem sequence_success_children {α β : Type} (first : Cursor → Spec.ParseResult α → Prop)
    (second : Cursor → Spec.ParseResult β → Prop) (cursor next : Cursor) (a : α) (b : β)
    (h : Spec.sequence first second cursor (.Ok (next, (a, b)))) :
    ∃ middle, first cursor (.Ok (middle, a)) ∧ second middle (.Ok (next, b)) := by
  rcases h with ⟨left, hleft, hresult⟩
  cases left with
  | Err _ => cases hresult
  | Ok pair =>
    rcases pair with ⟨middle, value⟩
    rcases hresult with ⟨right, hright, heq⟩
    cases right with
    | Err _ => cases heq
    | Ok pair =>
      rcases pair with ⟨after, other⟩
      cases heq
      exact ⟨middle, hleft, hright⟩

theorem left_success_children {α β : Type} (first : Cursor → Spec.ParseResult α → Prop)
    (second : Cursor → Spec.ParseResult β → Prop) (cursor next : Cursor) (value : α)
    (h : Spec.left first second cursor (.Ok (next, value))) :
    ∃ middle other, first cursor (.Ok (middle, value)) ∧ second middle (.Ok (next, other)) := by
  rcases map_success_value _ _ _ _ _ h with ⟨⟨a, b⟩, hseq, rfl⟩
  obtain ⟨middle, hfirst, hsecond⟩ := sequence_success_children _ _ _ _ value b hseq
  exact ⟨middle, b, hfirst, hsecond⟩

theorem right_success_children {α β : Type} (first : Cursor → Spec.ParseResult α → Prop)
    (second : Cursor → Spec.ParseResult β → Prop) (cursor next : Cursor) (value : β)
    (h : Spec.right first second cursor (.Ok (next, value))) :
    ∃ middle other, first cursor (.Ok (middle, other)) ∧ second middle (.Ok (next, value)) := by
  rcases map_success_value _ _ _ _ _ h with ⟨⟨a, b⟩, hseq, rfl⟩
  obtain ⟨middle, hfirst, hsecond⟩ := sequence_success_children _ _ _ _ a value hseq
  exact ⟨middle, a, hfirst, hsecond⟩

theorem middle_success_children {α β γ : Type} (before : Cursor → Spec.ParseResult α → Prop)
    (child : Cursor → Spec.ParseResult β → Prop) (after : Cursor → Spec.ParseResult γ → Prop)
    (cursor next : Cursor) (value : β)
    (h : Spec.middle before child after cursor (.Ok (next, value))) :
    ∃ first second a c, before cursor (.Ok (first, a)) ∧
      child first (.Ok (second, value)) ∧ after second (.Ok (next, c)) := by
  rcases map_success_value _ _ _ _ _ h with ⟨⟨a, b, c⟩, hseq, rfl⟩
  obtain ⟨first, hbefore, hrest⟩ := sequence_success_children _ _ _ _ a (value, c) hseq
  obtain ⟨second, hchild, hafter⟩ := sequence_success_children _ _ _ _ value c hrest
  exact ⟨first, second, a, c, hbefore, hchild, hafter⟩

theorem ignore_success_cursor {α : Type} (child : Cursor → Spec.ParseResult α → Prop)
    (cursor next : Cursor) (h : Spec.ignore child cursor (.Ok (next, ()))) :
    ∃ value, child cursor (.Ok (next, value)) := by
  obtain ⟨value, hchild, _⟩ := map_success_value _ _ _ _ _ h
  exact ⟨value, hchild⟩

end RustHammer.Proofs
