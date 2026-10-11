import RustHammer.BitsProofs

open RustHammer.Code.grammar.bytes
  RustHammer.Code.grammar.numeric
  RustHammer.Code.grammar.sequence
  RustHammer.Code.grammar.transform
  RustHammer.Code.input_types

open Aeneas Aeneas.Std Result WP

namespace RustHammer.Proofs
open Code

/-- The default complete entry point preserves a parser contract. -/
theorem complete_spec {P α : Type} (pi : parser_traits.Parser P α) (parser : P)
    (input : Slice U8) (cursor : Cursor) (contract : Spec.ParseResult α → Prop)
    (hp : pi.parse_with parser input cursor ByteOrder.Big ⦃ outcome => Spec.satisfies contract outcome ⦄) :
    parser_traits.Parser.parse.default pi parser input cursor ⦃ result => contract result ⦄ := by
  simpa only [parser_traits.Parser.parse.default, Spec.satisfies_iff] using hp

theorem bit_spec (input : Slice U8) (cursor : Cursor) :
    Bit.Insts.RusthammerParser_traitsParserInputBool.parse_with () input cursor ByteOrder.Big
      ⦃ result => Spec.satisfies (Spec.bitOutcome input cursor) result ⦄ := by
  simp only [Bit.Insts.RusthammerParser_traitsParserInputBool.parse_with,
    Spec.satisfies_iff]
  by_cases h : cursor.bit.val < 8 ∧ cursor.byte.val < input.val.length
  · simpa only [Spec.bitOutcome, if_pos h] using read_bit_success input cursor h.1 h.2
  · simpa only [Spec.bitOutcome, if_neg h] using read_bit_failure input cursor h

theorem bits_spec (parser : Bits) (input : Slice U8) (cursor : Cursor)
    (hconfig : Spec.validBits parser) :
    Bits.Insts.RusthammerParser_traitsParserInputU64.parse_with parser input cursor ByteOrder.Big
      ⦃ result => Spec.satisfies (Spec.bitsOutcome input cursor parser.width) result ⦄ := by
  simpa only [Bits.Insts.RusthammerParser_traitsParserInputU64.parse_with,
    read_ordered_bits, Spec.satisfies_iff] using read_bits_spec input cursor parser hconfig

theorem take_aligned_parser_spec (parser : TakeAligned) (input : Slice U8) (cursor : Cursor) :
    TakeAligned.Insts.RusthammerParser_traitsParserInputSharedInputSliceU8.parse_with parser input cursor ByteOrder.Big
      ⦃ result => Spec.satisfies (Spec.takeAlignedOutcome input cursor parser.count) result ⦄ := by
  simpa only [TakeAligned.Insts.RusthammerParser_traitsParserInputSharedInputSliceU8.parse_with,
    Spec.satisfies_iff] using take_aligned_spec input cursor parser.count

/-- Default-order sequencing satisfies the shared relation. -/
theorem seq_spec {P Q α β : Type} (pi : parser_traits.Parser P α) (qi : parser_traits.Parser Q β)
    (parser : Seq P Q) (input : Slice U8) (cursor : Cursor)
    (first : Cursor → Spec.ParseResult α → Prop)
    (second : Cursor → Spec.ParseResult β → Prop)
    (hp : ∀ start, pi.parse_with parser.first input start ByteOrder.Big
      ⦃ result => Spec.satisfies (first start) result ⦄)
    (hq : ∀ start, qi.parse_with parser.second input start ByteOrder.Big
      ⦃ result => Spec.satisfies (second start) result ⦄) :
    Seq.Insts.RusthammerParser_traitsParserInputPair.parse_with pi qi parser input cursor ByteOrder.Big
      ⦃ result => Spec.satisfies (Spec.sequence first second cursor) result ⦄ := by
  rw [Seq.Insts.RusthammerParser_traitsParserInputPair.parse_with]
  step with hp cursor as ⟨outcome, houtcome⟩
  rcases houtcome with ⟨left, hleft, heq⟩
  subst outcome

  cases left with
  | Err error =>
    simp only [spec_ok, Spec.satisfies_error]
    exact ⟨.Err error, hleft, rfl⟩
  | Ok pair =>
    rcases pair with ⟨middle, a⟩
    dsimp only

    step with hq middle as ⟨outcome, houtcome⟩
    rcases houtcome with ⟨right, hright, heq⟩
    subst outcome

    cases right with
    | Err error =>
      simp only [spec_ok, Spec.satisfies_error]
      exact ⟨.Ok (middle, a), hleft, .Err error, hright, rfl⟩
    | Ok pair =>
      rcases pair with ⟨last, b⟩
      dsimp only
      change (ok (.Ok (last, (a, b))) : Result (Spec.ParseResult (α × β)))
        ⦃ result => Spec.satisfies (Spec.sequence first second cursor) result ⦄
      simp only [spec_ok, Spec.satisfies_success]
      exact ⟨.Ok (middle, a), hleft, .Ok (last, b), hright, rfl⟩

theorem map_spec {P F α β : Type} (pi : parser_traits.Parser P α) (fi : core.ops.function.Fn F α β)
    (parser : Map P F) (input : Slice U8) (cursor : Cursor)
    (child : Cursor → Spec.ParseResult α → Prop) (mapping : α → β → Prop)
    (hp : pi.parse_with parser.parser input cursor ByteOrder.Big
      ⦃ result => Spec.satisfies (child cursor) result ⦄)
    (hf : ∀ next value, child cursor (.Ok (next, value)) →
      fi.call parser.map value ⦃ result => mapping value result ⦄) :
    Map.Insts.RusthammerParser_traitsParser.parse_with pi fi parser input cursor ByteOrder.Big
      ⦃ result => Spec.satisfies (Spec.map child mapping cursor) result ⦄ := by
  rw [Map.Insts.RusthammerParser_traitsParser.parse_with]
  step with hp as ⟨outcome, houtcome⟩
  rcases houtcome with ⟨parsed, hparsed, heq⟩
  subst outcome

  cases parsed with
  | Err error =>
    simp only [spec_ok, Spec.satisfies_error]
    exact ⟨.Err error, hparsed, rfl⟩
  | Ok pair =>
    rcases pair with ⟨next, value⟩
    dsimp only

    step with hf next value hparsed as ⟨mapped, hmapped⟩
    simp only [Spec.satisfies_success]
    exact ⟨.Ok (next, value), hparsed, mapped, hmapped, rfl⟩

theorem verify_spec {P F α : Type} (pi : parser_traits.Parser P α) (fi : core.ops.function.Fn F α Bool)
    (parser : Verify P F) (input : Slice U8) (cursor : Cursor)
    (child : Cursor → Spec.ParseResult α → Prop) (predicate : α → Prop)
    [DecidablePred predicate]
    (hp : pi.parse_with parser.parser input cursor ByteOrder.Big
      ⦃ result => Spec.satisfies (child cursor) result ⦄)
    (hf : ∀ next value, child cursor (.Ok (next, value)) →
      fi.call parser.predicate value ⦃ result => result = decide (predicate value) ⦄) :
    Verify.Insts.RusthammerParser_traitsParser.parse_with pi fi parser input cursor ByteOrder.Big
      ⦃ result => Spec.satisfies (Spec.verify child predicate cursor) result ⦄ := by
  rw [Verify.Insts.RusthammerParser_traitsParser.parse_with]
  step with hp as ⟨outcome, houtcome⟩
  rcases houtcome with ⟨parsed, hparsed, heq⟩
  subst outcome

  cases parsed with
  | Err error =>
    simp only [spec_ok, Spec.satisfies_error]
    exact ⟨.Err error, hparsed, rfl⟩
  | Ok pair =>
    rcases pair with ⟨next, value⟩
    dsimp only

    step with hf next value hparsed as ⟨accepted, haccepted⟩
    by_cases hpred : predicate value
    · have htrue : accepted = true := by simpa [hpred] using haccepted
      simp only [htrue, ↓reduceIte, spec_ok, Spec.satisfies_success]
      exact ⟨.Ok (next, value), hparsed, by simp [hpred]⟩
    · have hfalse : accepted = false := by simpa [hpred] using haccepted
      simp only [hfalse, Bool.false_eq_true, ↓reduceIte, spec_ok, Spec.satisfies_error]
      exact ⟨.Ok (next, value), hparsed, by simp [hpred]⟩

end RustHammer.Proofs
