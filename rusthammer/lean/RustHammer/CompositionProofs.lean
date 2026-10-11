import RustHammer.CompositionSpec
import RustHammer.ParserProofs

open RustHammer.Code.grammar.control
  RustHammer.Code.grammar.transform
  RustHammer.Code.input_types

open Aeneas Aeneas.Std Result WP

namespace RustHammer.Proofs
open Code

/-- Neither empty nor failing grammars require a valid cursor or final input. -/
theorem epsilon_with_spec (input : Slice U8) (cursor : Cursor) (context : ByteOrder) :
    Epsilon.Insts.RusthammerParser_traitsParserInputTuple.parse_with () input cursor context
      ⦃ result => Contracts.epsilon cursor result ⦄ := by
  simp [Epsilon.Insts.RusthammerParser_traitsParserInputTuple.parse_with, Contracts.epsilon, spec_ok]

theorem epsilon_final_spec (input : Slice U8) (cursor : Cursor) :
    Epsilon.Insts.RusthammerParser_traitsParserInputTuple.parse_with () input cursor ByteOrder.Big
      ⦃ result => Spec.satisfies (Spec.epsilon cursor) result ⦄ := by
  simp [Epsilon.Insts.RusthammerParser_traitsParserInputTuple.parse_with,
    Spec.epsilon, spec_ok]

theorem epsilon_spec (input : Slice U8) (cursor : Cursor) :
    parser_traits.Parser.parse.default Epsilon.Insts.RusthammerParser_traitsParserInputTuple () input cursor
      ⦃ result => Spec.epsilon cursor result ⦄ :=
  complete_spec Epsilon.Insts.RusthammerParser_traitsParserInputTuple () input cursor
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
    (cursor : Cursor) (context : ByteOrder) :
    Fail.Insts.RusthammerParser_traitsParser.parse_with parser input cursor context
      ⦃ result => Contracts.fail result ⦄ := by
  simp [Fail.Insts.RusthammerParser_traitsParser.parse_with, Contracts.fail, spec_ok]

theorem fail_final_spec {α : Type} (parser : Fail α) (input : Slice U8) (cursor : Cursor) :
    Fail.Insts.RusthammerParser_traitsParser.parse_with parser input cursor ByteOrder.Big
      ⦃ result => Spec.satisfies Spec.fail result ⦄ := by
  simp [Fail.Insts.RusthammerParser_traitsParser.parse_with, Spec.fail, spec_ok]

theorem fail_spec {α : Type} (parser : Fail α) (input : Slice U8) (cursor : Cursor) :
    parser_traits.Parser.parse.default (Fail.Insts.RusthammerParser_traitsParser α) parser input cursor
      ⦃ result => Spec.fail result ⦄ :=
  complete_spec (Fail.Insts.RusthammerParser_traitsParser α) parser input cursor
    Spec.fail (fail_final_spec parser input cursor)

theorem try_map_with_spec {P F α β ε : Type} (pi : parser_traits.Parser P α)
    (fi : core.ops.function.Fn F α (core.result.Result β ε))
    (parser : TryMap P F) (input : Slice U8) (cursor : Cursor) (context : ByteOrder)
    (child : Cursor → Spec.ParseResult α → Prop) (mapping : α → core.result.Result β ε → Prop)
    (hp : pi.parse_with parser.parser input cursor context ⦃ result => child cursor result ⦄)
    (hf : ∀ next value, child cursor (.Ok (next, value)) →
      fi.call parser.map value ⦃ result => mapping value result ⦄) :
    TryMap.Insts.RusthammerParser_traitsParser.parse_with pi fi parser input cursor context
      ⦃ result => Contracts.tryMap child mapping cursor result ⦄ := by
  rw [TryMap.Insts.RusthammerParser_traitsParser.parse_with]
  step with hp as ⟨parsed, hparsed⟩
  cases parsed with
  | Err error => simp only [spec_ok]; exact ⟨.Err error, hparsed, rfl⟩
  | Ok pair =>
    rcases pair with ⟨next, value⟩
    step with hf next value hparsed as ⟨mapped, hmapped⟩
    cases mapped with
    | Ok converted =>
      simp only [spec_ok]
      exact ⟨.Ok (next, value), hparsed, .Ok converted, hmapped, rfl⟩
    | Err error =>
      simp only [spec_ok]
      exact ⟨.Ok (next, value), hparsed, .Err error, hmapped, rfl⟩

theorem try_map_final_spec {P F α β ε : Type} (pi : parser_traits.Parser P α)
    (fi : core.ops.function.Fn F α (core.result.Result β ε))
    (parser : TryMap P F) (input : Slice U8) (cursor : Cursor)
    (child : Cursor → Spec.ParseResult α → Prop) (mapping : α → core.result.Result β ε → Prop)
    (hp : pi.parse_with parser.parser input cursor ByteOrder.Big
      ⦃ result => Spec.satisfies (child cursor) result ⦄)
    (hf : ∀ next value, child cursor (.Ok (next, value)) →
      fi.call parser.map value ⦃ result => mapping value result ⦄) :
    TryMap.Insts.RusthammerParser_traitsParser.parse_with pi fi parser input cursor ByteOrder.Big
      ⦃ result => Spec.satisfies (Spec.tryMap child mapping cursor) result ⦄ := by
  rw [TryMap.Insts.RusthammerParser_traitsParser.parse_with]
  step with hp as ⟨outcome, houtcome⟩
  rcases houtcome with ⟨parsed, hparsed, heq⟩
  subst outcome

  cases parsed with
  | Err error =>
    simp only [spec_ok, Spec.satisfies_error]
    exact ⟨.Err error, hparsed, rfl⟩
  | Ok pair =>
    rcases pair with ⟨next, value⟩

    step with hf next value hparsed as ⟨mapped, hmapped⟩
    cases mapped with
    | Ok converted =>
      simp only [spec_ok, Spec.satisfies_success]
      exact ⟨.Ok (next, value), hparsed, .Ok converted, hmapped, rfl⟩
    | Err error =>
      simp only [spec_ok, Spec.satisfies_error]
      exact ⟨.Ok (next, value), hparsed, .Err error, hmapped, rfl⟩

theorem try_map_spec {P F α β ε : Type} (pi : parser_traits.Parser P α)
    (fi : core.ops.function.Fn F α (core.result.Result β ε))
    (parser : TryMap P F) (input : Slice U8) (cursor : Cursor)
    (child : Cursor → Spec.ParseResult α → Prop) (mapping : α → core.result.Result β ε → Prop)
    (hp : pi.parse_with parser.parser input cursor ByteOrder.Big
      ⦃ result => Spec.satisfies (child cursor) result ⦄)
    (hf : ∀ next value, child cursor (.Ok (next, value)) →
      fi.call parser.map value ⦃ result => mapping value result ⦄) :
    parser_traits.Parser.parse.default (TryMap.Insts.RusthammerParser_traitsParser pi fi) parser input cursor
      ⦃ result => Spec.tryMap child mapping cursor result ⦄ :=
  complete_spec (TryMap.Insts.RusthammerParser_traitsParser pi fi) parser input cursor
    (Spec.tryMap child mapping cursor)
    (try_map_final_spec pi fi parser input cursor child mapping hp hf)

/-- Skipped callbacks need no correctness or termination assumption. -/
theorem try_map_child_error {P F α β ε : Type} (pi : parser_traits.Parser P α)
    (fi : core.ops.function.Fn F α (core.result.Result β ε))
    (parser : TryMap P F) (input : Slice U8) (cursor : Cursor) (context : ByteOrder)
    (error : ParseError)
    (hp : pi.parse_with parser.parser input cursor context ⦃ result => result = .Err error ⦄) :
    TryMap.Insts.RusthammerParser_traitsParser.parse_with pi fi parser input cursor context
      ⦃ result => result = .Err error ⦄ := by
  rw [TryMap.Insts.RusthammerParser_traitsParser.parse_with]
  step with hp as ⟨parsed, hparsed⟩
  simp [hparsed, spec_ok]

/-- Successful conversion preserves exactly the successful child's cursor. -/
theorem try_map_success_child {α β ε : Type}
    (child : Cursor → Spec.ParseResult α → Prop) (mapping : α → core.result.Result β ε → Prop)
    (cursor next : Cursor) (converted : β)
    (h : Contracts.tryMap child mapping cursor (.Ok (next, converted))) :
    ∃ value, child cursor (.Ok (next, value)) ∧ mapping value (.Ok converted) := by
  rcases h with ⟨parsed, hparsed, houtcome⟩
  cases parsed with
  | Err error => cases houtcome
  | Ok pair =>
    rcases pair with ⟨last, value⟩
    rcases houtcome with ⟨mapped, hmapped, houtcome⟩
    cases mapped with
    | Err error => cases houtcome
    | Ok output =>
      cases houtcome
      exact ⟨value, hparsed, hmapped⟩

end RustHammer.Proofs
