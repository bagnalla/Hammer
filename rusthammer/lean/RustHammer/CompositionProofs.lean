import RustHammer.CompositionSpec
import RustHammer.PartialProofs

open Aeneas Aeneas.Std Result WP

namespace RustHammer.Proofs
open Code

/-- Neither empty nor failing grammars require a valid cursor or final input. -/
theorem epsilon_with_spec (input : Slice U8) (cursor : Cursor) (status : InputStatus) :
    Epsilon.Insts.RusthammerParserInputTuple.parse_with () input cursor status
      ⦃ result => Partial.epsilon cursor result ⦄ := by
  simp [Epsilon.Insts.RusthammerParserInputTuple.parse_with, Partial.epsilon, spec_ok]

theorem epsilon_final_spec (input : Slice U8) (cursor : Cursor) :
    Epsilon.Insts.RusthammerParserInputTuple.parse_with () input cursor .Final
      ⦃ result => Spec.completed (Spec.epsilon cursor) result ⦄ := by
  simp [Epsilon.Insts.RusthammerParserInputTuple.parse_with, Spec.completed_success,
    Spec.epsilon, spec_ok]

theorem epsilon_spec (input : Slice U8) (cursor : Cursor) :
    Parser.parse.default Epsilon.Insts.RusthammerParserInputTuple () input cursor
      ⦃ result => Spec.epsilon cursor result ⦄ :=
  complete_spec Epsilon.Insts.RusthammerParserInputTuple () input cursor
    (Spec.epsilon cursor) (epsilon_final_spec input cursor)

theorem fail_new_spec (α : Type) :
    Fail.new α ⦃ result => result = { output := () } ⦄ := by
  simp [Fail.new, spec_ok]

theorem fail_default_spec (α : Type) :
    Fail.Insts.CoreDefaultDefault.default α ⦃ result => result = { output := () } ⦄ :=
  fail_new_spec α

theorem fail_clone_spec {α : Type} (parser : Fail α) :
    Fail.Insts.CoreCloneClone.clone parser ⦃ result => result = parser ⦄ := by
  simp [Fail.Insts.CoreCloneClone.clone, spec_ok]

theorem fail_with_spec {α : Type} (parser : Fail α) (input : Slice U8)
    (cursor : Cursor) (status : InputStatus) :
    Fail.Insts.RusthammerParser.parse_with parser input cursor status
      ⦃ result => Partial.fail result ⦄ := by
  simp [Fail.Insts.RusthammerParser.parse_with, Partial.fail, spec_ok]

theorem fail_final_spec {α : Type} (parser : Fail α) (input : Slice U8) (cursor : Cursor) :
    Fail.Insts.RusthammerParser.parse_with parser input cursor .Final
      ⦃ result => Spec.completed Spec.fail result ⦄ := by
  simp [Fail.Insts.RusthammerParser.parse_with, Spec.completed_error, Spec.fail, spec_ok]

theorem fail_spec {α : Type} (parser : Fail α) (input : Slice U8) (cursor : Cursor) :
    Parser.parse.default (Fail.Insts.RusthammerParser α) parser input cursor
      ⦃ result => Spec.fail result ⦄ :=
  complete_spec (Fail.Insts.RusthammerParser α) parser input cursor
    Spec.fail (fail_final_spec parser input cursor)

theorem try_map_with_spec {P F α β ε : Type} (pi : Parser P α)
    (fi : core.ops.function.Fn F α (core.result.Result β ε))
    (parser : TryMap P F) (input : Slice U8) (cursor : Cursor) (status : InputStatus)
    (child : Cursor → ParseOutcome α → Prop) (mapping : α → core.result.Result β ε → Prop)
    (hp : pi.parse_with parser.parser input cursor status ⦃ result => child cursor result ⦄)
    (hf : ∀ next value, child cursor (.Success next value) →
      fi.call parser.map value ⦃ result => mapping value result ⦄) :
    TryMap.Insts.RusthammerParser.parse_with pi fi parser input cursor status
      ⦃ result => Partial.tryMap child mapping cursor result ⦄ := by
  unfold TryMap.Insts.RusthammerParser.parse_with
  step with hp as ⟨parsed, hparsed⟩
  cases parsed with
  | NeedMore => simp only [spec_ok]; exact ⟨.NeedMore, hparsed, rfl⟩
  | Error error => simp only [spec_ok]; exact ⟨.Error error, hparsed, rfl⟩
  | Success next value =>
    step with hf next value hparsed as ⟨mapped, hmapped⟩
    cases mapped with
    | Ok converted =>
      simp only [spec_ok]
      exact ⟨.Success next value, hparsed, .Ok converted, hmapped, rfl⟩
    | Err error =>
      simp only [spec_ok]
      exact ⟨.Success next value, hparsed, .Err error, hmapped, rfl⟩

theorem try_map_final_spec {P F α β ε : Type} (pi : Parser P α)
    (fi : core.ops.function.Fn F α (core.result.Result β ε))
    (parser : TryMap P F) (input : Slice U8) (cursor : Cursor)
    (child : Cursor → Spec.ParseResult α → Prop) (mapping : α → core.result.Result β ε → Prop)
    (hp : pi.parse_with parser.parser input cursor .Final
      ⦃ result => Spec.completed (child cursor) result ⦄)
    (hf : ∀ next value, child cursor (.Ok (next, value)) →
      fi.call parser.map value ⦃ result => mapping value result ⦄) :
    TryMap.Insts.RusthammerParser.parse_with pi fi parser input cursor .Final
      ⦃ result => Spec.completed (Spec.tryMap child mapping cursor) result ⦄ := by
  unfold TryMap.Insts.RusthammerParser.parse_with
  step with hp as ⟨outcome, houtcome⟩
  rcases houtcome with ⟨parsed, hparsed, rfl⟩
  cases parsed with
  | Err error =>
    simp only [Spec.completedResult, spec_ok, Spec.completed_error]
    exact ⟨.Err error, hparsed, rfl⟩
  | Ok pair =>
    rcases pair with ⟨next, value⟩
    simp only [Spec.completedResult]
    step with hf next value hparsed as ⟨mapped, hmapped⟩
    cases mapped with
    | Ok converted =>
      simp only [spec_ok, Spec.completed_success]
      exact ⟨.Ok (next, value), hparsed, .Ok converted, hmapped, rfl⟩
    | Err error =>
      simp only [spec_ok, Spec.completed_error]
      exact ⟨.Ok (next, value), hparsed, .Err error, hmapped, rfl⟩

theorem try_map_spec {P F α β ε : Type} (pi : Parser P α)
    (fi : core.ops.function.Fn F α (core.result.Result β ε))
    (parser : TryMap P F) (input : Slice U8) (cursor : Cursor)
    (child : Cursor → Spec.ParseResult α → Prop) (mapping : α → core.result.Result β ε → Prop)
    (hp : pi.parse_with parser.parser input cursor .Final
      ⦃ result => Spec.completed (child cursor) result ⦄)
    (hf : ∀ next value, child cursor (.Ok (next, value)) →
      fi.call parser.map value ⦃ result => mapping value result ⦄) :
    Parser.parse.default (TryMap.Insts.RusthammerParser pi fi) parser input cursor
      ⦃ result => Spec.tryMap child mapping cursor result ⦄ :=
  complete_spec (TryMap.Insts.RusthammerParser pi fi) parser input cursor
    (Spec.tryMap child mapping cursor)
    (try_map_final_spec pi fi parser input cursor child mapping hp hf)

/-- Skipped callbacks need no correctness or termination assumption. -/
theorem try_map_child_error {P F α β ε : Type} (pi : Parser P α)
    (fi : core.ops.function.Fn F α (core.result.Result β ε))
    (parser : TryMap P F) (input : Slice U8) (cursor : Cursor) (status : InputStatus)
    (error : ParseError)
    (hp : pi.parse_with parser.parser input cursor status ⦃ result => result = .Error error ⦄) :
    TryMap.Insts.RusthammerParser.parse_with pi fi parser input cursor status
      ⦃ result => result = .Error error ⦄ := by
  unfold TryMap.Insts.RusthammerParser.parse_with
  step with hp as ⟨parsed, hparsed⟩
  simp [hparsed, spec_ok]

theorem try_map_need_more {P F α β ε : Type} (pi : Parser P α)
    (fi : core.ops.function.Fn F α (core.result.Result β ε))
    (parser : TryMap P F) (input : Slice U8) (cursor : Cursor) (status : InputStatus)
    (hp : pi.parse_with parser.parser input cursor status ⦃ result => result = .NeedMore ⦄) :
    TryMap.Insts.RusthammerParser.parse_with pi fi parser input cursor status
      ⦃ result => result = .NeedMore ⦄ := by
  unfold TryMap.Insts.RusthammerParser.parse_with
  step with hp as ⟨parsed, hparsed⟩
  simp [hparsed, spec_ok]

/-- Successful conversion preserves exactly the successful child's cursor. -/
theorem try_map_success_child {α β ε : Type}
    (child : Cursor → ParseOutcome α → Prop) (mapping : α → core.result.Result β ε → Prop)
    (cursor next : Cursor) (converted : β)
    (h : Partial.tryMap child mapping cursor (.Success next converted)) :
    ∃ value, child cursor (.Success next value) ∧ mapping value (.Ok converted) := by
  rcases h with ⟨parsed, hparsed, houtcome⟩
  cases parsed with
  | NeedMore => cases houtcome
  | Error error => cases houtcome
  | Success last value =>
    rcases houtcome with ⟨mapped, hmapped, houtcome⟩
    cases mapped with
    | Err error => cases houtcome
    | Ok output =>
      cases houtcome
      exact ⟨value, hparsed, hmapped⟩

end RustHammer.Proofs
