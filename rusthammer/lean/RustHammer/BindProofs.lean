import RustHammer.BindSpec
import RustHammer.PartialProofs

open Aeneas Aeneas.Std Result WP

namespace RustHammer.Proofs
open Code

/-- Factory and second-parser contracts are needed only for reachable first
successes. The factory's invariant can express validated configuration or borrowing. -/
theorem bind_with_spec {P F Q α β : Type} (pi : Parser P α)
    (fi : core.ops.function.Fn F α Q) (qi : Parser Q β)
    (parser : Bind P F) (input : Slice U8) (cursor : Cursor) (status : InputStatus)
    (first : Cursor → ParseOutcome α → Prop) (second : α → Cursor → ParseOutcome β → Prop)
    (constructed : α → Q → Prop)
    (hp : pi.parse_with parser.parser input cursor status ⦃ result => first cursor result ⦄)
    (hf : ∀ next value, first cursor (.Success next value) →
      fi.call parser.then value ⦃ result => constructed value result ⦄)
    (hq : ∀ next value child, first cursor (.Success next value) → constructed value child →
      qi.parse_with child input next status ⦃ result => second value next result ⦄) :
    Bind.Insts.RusthammerParser.parse_with pi fi qi parser input cursor status
      ⦃ result => Partial.bind first second cursor result ⦄ := by
  unfold Bind.Insts.RusthammerParser.parse_with
  step with hp as ⟨parsed, hparsed⟩
  cases parsed with
  | NeedMore => simp only [spec_ok]; exact ⟨.NeedMore, hparsed, rfl⟩
  | Error error => simp only [spec_ok]; exact ⟨.Error error, hparsed, rfl⟩
  | Success next value =>
    step with hf next value hparsed as ⟨child, hchild⟩
    step with hq next value child hparsed hchild as ⟨outcome, houtcome⟩
    exact ⟨.Success next value, hparsed, houtcome⟩

theorem bind_final_spec {P F Q α β : Type} (pi : Parser P α)
    (fi : core.ops.function.Fn F α Q) (qi : Parser Q β)
    (parser : Bind P F) (input : Slice U8) (cursor : Cursor)
    (first : Cursor → Spec.ParseResult α → Prop) (second : α → Cursor → Spec.ParseResult β → Prop)
    (constructed : α → Q → Prop)
    (hp : pi.parse_with parser.parser input cursor .Final ⦃ result => Spec.completed (first cursor) result ⦄)
    (hf : ∀ next value, first cursor (.Ok (next, value)) →
      fi.call parser.then value ⦃ result => constructed value result ⦄)
    (hq : ∀ next value child, first cursor (.Ok (next, value)) → constructed value child →
      qi.parse_with child input next .Final ⦃ result => Spec.completed (second value next) result ⦄) :
    Bind.Insts.RusthammerParser.parse_with pi fi qi parser input cursor .Final
      ⦃ result => Spec.completed (Spec.bind first second cursor) result ⦄ := by
  unfold Bind.Insts.RusthammerParser.parse_with
  step with hp as ⟨outcome, houtcome⟩
  rcases houtcome with ⟨parsed, hparsed, rfl⟩
  cases parsed with
  | Err error =>
    simp only [Spec.completedResult, spec_ok, Spec.completed_error]
    exact ⟨.Err error, hparsed, rfl⟩
  | Ok pair =>
    rcases pair with ⟨next, value⟩
    simp only [Spec.completedResult]
    step with hf next value hparsed as ⟨child, hchild⟩
    step with hq next value child hparsed hchild as ⟨outcome, hcompleted⟩
    rcases hcompleted with ⟨result, hresult, houtcome⟩
    exact ⟨result, ⟨.Ok (next, value), hparsed, hresult⟩, houtcome⟩

theorem bind_spec {P F Q α β : Type} (pi : Parser P α)
    (fi : core.ops.function.Fn F α Q) (qi : Parser Q β)
    (parser : Bind P F) (input : Slice U8) (cursor : Cursor)
    (first : Cursor → Spec.ParseResult α → Prop) (second : α → Cursor → Spec.ParseResult β → Prop)
    (constructed : α → Q → Prop)
    (hp : pi.parse_with parser.parser input cursor .Final ⦃ result => Spec.completed (first cursor) result ⦄)
    (hf : ∀ next value, first cursor (.Ok (next, value)) →
      fi.call parser.then value ⦃ result => constructed value result ⦄)
    (hq : ∀ next value child, first cursor (.Ok (next, value)) → constructed value child →
      qi.parse_with child input next .Final ⦃ result => Spec.completed (second value next) result ⦄) :
    Parser.parse.default (Bind.Insts.RusthammerParser pi fi qi) parser input cursor
      ⦃ result => Spec.bind first second cursor result ⦄ :=
  complete_spec (Bind.Insts.RusthammerParser pi fi qi) parser input cursor
    (Spec.bind first second cursor)
    (bind_final_spec pi fi qi parser input cursor first second constructed hp hf hq)

/-- Skipping a factory needs no assumption about it or any constructed parser. -/
theorem bind_first_error {P F Q α β : Type} (pi : Parser P α)
    (fi : core.ops.function.Fn F α Q) (qi : Parser Q β)
    (parser : Bind P F) (input : Slice U8) (cursor : Cursor) (status : InputStatus) (error : ParseError)
    (hp : pi.parse_with parser.parser input cursor status ⦃ result => result = .Error error ⦄) :
    Bind.Insts.RusthammerParser.parse_with pi fi qi parser input cursor status
      ⦃ result => result = .Error error ⦄ := by
  unfold Bind.Insts.RusthammerParser.parse_with
  step with hp as ⟨parsed, hparsed⟩
  simp [hparsed, spec_ok]

theorem bind_first_need_more {P F Q α β : Type} (pi : Parser P α)
    (fi : core.ops.function.Fn F α Q) (qi : Parser Q β)
    (parser : Bind P F) (input : Slice U8) (cursor : Cursor) (status : InputStatus)
    (hp : pi.parse_with parser.parser input cursor status ⦃ result => result = .NeedMore ⦄) :
    Bind.Insts.RusthammerParser.parse_with pi fi qi parser input cursor status
      ⦃ result => result = .NeedMore ⦄ := by
  unfold Bind.Insts.RusthammerParser.parse_with
  step with hp as ⟨parsed, hparsed⟩
  simp [hparsed, spec_ok]

theorem bind_success_children {α β : Type} (first : Cursor → ParseOutcome α → Prop)
    (second : α → Cursor → ParseOutcome β → Prop) (cursor next : Cursor) (value : β)
    (h : Partial.bind first second cursor (.Success next value)) :
    ∃ middle prior, first cursor (.Success middle prior) ∧ second prior middle (.Success next value) := by
  rcases h with ⟨parsed, hparsed, hrest⟩
  cases parsed with
  | NeedMore => cases hrest
  | Error error => cases hrest
  | Success middle prior => exact ⟨middle, prior, hparsed, hrest⟩

end RustHammer.Proofs
