import RustHammer.BindSpec
import RustHammer.ParserProofs

open RustHammer.Code.grammar.sequence
  RustHammer.Code.input_types

open Aeneas Aeneas.Std Result WP

namespace RustHammer.Proofs
open Code

/-- Factory and second-parser contracts are needed only for reachable first
successes. The factory's invariant can express validated configuration or borrowing. -/
theorem bind_with_spec {P F Q α β : Type} (pi : parser_traits.Parser P α)
    (fi : core.ops.function.Fn F α Q) (qi : parser_traits.Parser Q β)
    (parser : Bind P F) (input : Slice U8) (cursor : Cursor) (context : ByteOrder)
    (first : Cursor → Spec.ParseResult α → Prop) (second : α → Cursor → Spec.ParseResult β → Prop)
    (constructed : α → Q → Prop)
    (hp : pi.parse_with parser.parser input cursor context ⦃ result => first cursor result ⦄)
    (hf : ∀ next value, first cursor (.Ok (next, value)) →
      fi.call parser.then value ⦃ result => constructed value result ⦄)
    (hq : ∀ next value child, first cursor (.Ok (next, value)) → constructed value child →
      qi.parse_with child input next context ⦃ result => second value next result ⦄) :
    Bind.Insts.RusthammerParser_traitsParser.parse_with pi fi qi parser input cursor context
      ⦃ result => Contracts.bind first second cursor result ⦄ := by
  rw [Bind.Insts.RusthammerParser_traitsParser.parse_with]
  step with hp as ⟨parsed, hparsed⟩
  cases parsed with
  | Err error => simp only [spec_ok]; exact ⟨.Err error, hparsed, rfl⟩
  | Ok pair =>
    rcases pair with ⟨next, value⟩
    step with hf next value hparsed as ⟨child, hchild⟩
    step with hq next value child hparsed hchild as ⟨outcome, houtcome⟩
    exact ⟨.Ok (next, value), hparsed, houtcome⟩

theorem bind_final_spec {P F Q α β : Type} (pi : parser_traits.Parser P α)
    (fi : core.ops.function.Fn F α Q) (qi : parser_traits.Parser Q β)
    (parser : Bind P F) (input : Slice U8) (cursor : Cursor)
    (first : Cursor → Spec.ParseResult α → Prop) (second : α → Cursor → Spec.ParseResult β → Prop)
    (constructed : α → Q → Prop)
    (hp : pi.parse_with parser.parser input cursor ByteOrder.Big ⦃ result => Spec.satisfies (first cursor) result ⦄)
    (hf : ∀ next value, first cursor (.Ok (next, value)) →
      fi.call parser.then value ⦃ result => constructed value result ⦄)
    (hq : ∀ next value child, first cursor (.Ok (next, value)) → constructed value child →
      qi.parse_with child input next ByteOrder.Big ⦃ result => Spec.satisfies (second value next) result ⦄) :
    Bind.Insts.RusthammerParser_traitsParser.parse_with pi fi qi parser input cursor ByteOrder.Big
      ⦃ result => Spec.satisfies (Spec.bind first second cursor) result ⦄ := by
  rw [Bind.Insts.RusthammerParser_traitsParser.parse_with]
  step with hp as ⟨outcome, houtcome⟩
  rcases houtcome with ⟨parsed, hparsed, heq⟩
  subst outcome

  cases parsed with
  | Err error =>
    simp only [spec_ok, Spec.satisfies_error]
    exact ⟨.Err error, hparsed, rfl⟩
  | Ok pair =>
    rcases pair with ⟨next, value⟩

    step with hf next value hparsed as ⟨child, hchild⟩
    step with hq next value child hparsed hchild as ⟨outcome, hcompleted⟩
    rcases hcompleted with ⟨result, hresult, houtcome⟩
    exact ⟨result, ⟨.Ok (next, value), hparsed, hresult⟩, houtcome⟩

theorem bind_spec {P F Q α β : Type} (pi : parser_traits.Parser P α)
    (fi : core.ops.function.Fn F α Q) (qi : parser_traits.Parser Q β)
    (parser : Bind P F) (input : Slice U8) (cursor : Cursor)
    (first : Cursor → Spec.ParseResult α → Prop) (second : α → Cursor → Spec.ParseResult β → Prop)
    (constructed : α → Q → Prop)
    (hp : pi.parse_with parser.parser input cursor ByteOrder.Big ⦃ result => Spec.satisfies (first cursor) result ⦄)
    (hf : ∀ next value, first cursor (.Ok (next, value)) →
      fi.call parser.then value ⦃ result => constructed value result ⦄)
    (hq : ∀ next value child, first cursor (.Ok (next, value)) → constructed value child →
      qi.parse_with child input next ByteOrder.Big ⦃ result => Spec.satisfies (second value next) result ⦄) :
    parser_traits.Parser.parse.default (Bind.Insts.RusthammerParser_traitsParser pi fi qi) parser input cursor
      ⦃ result => Spec.bind first second cursor result ⦄ :=
  complete_spec (Bind.Insts.RusthammerParser_traitsParser pi fi qi) parser input cursor
    (Spec.bind first second cursor)
    (bind_final_spec pi fi qi parser input cursor first second constructed hp hf hq)

/-- Skipping a factory needs no assumption about it or any constructed parser. -/
theorem bind_first_error {P F Q α β : Type} (pi : parser_traits.Parser P α)
    (fi : core.ops.function.Fn F α Q) (qi : parser_traits.Parser Q β)
    (parser : Bind P F) (input : Slice U8) (cursor : Cursor) (context : ByteOrder) (error : ParseError)
    (hp : pi.parse_with parser.parser input cursor context ⦃ result => result = .Err error ⦄) :
    Bind.Insts.RusthammerParser_traitsParser.parse_with pi fi qi parser input cursor context
      ⦃ result => result = .Err error ⦄ := by
  rw [Bind.Insts.RusthammerParser_traitsParser.parse_with]
  step with hp as ⟨parsed, hparsed⟩
  simp [hparsed, spec_ok]

theorem bind_success_children {α β : Type} (first : Cursor → Spec.ParseResult α → Prop)
    (second : α → Cursor → Spec.ParseResult β → Prop) (cursor next : Cursor) (value : β)
    (h : Contracts.bind first second cursor (.Ok (next, value))) :
    ∃ middle prior, first cursor (.Ok (middle, prior)) ∧ second prior middle (.Ok (next, value)) := by
  rcases h with ⟨parsed, hparsed, hrest⟩
  cases parsed with
  | Err error => cases hrest
  | Ok pair =>
    rcases pair with ⟨middle, prior⟩
    exact ⟨middle, prior, hparsed, hrest⟩

end RustHammer.Proofs
