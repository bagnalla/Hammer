import RustHammer.BitsProofs

open Aeneas Aeneas.Std Result WP

namespace RustHammer.Proofs
open Code

theorem classify_final_spec {α : Type} (result : Spec.ParseResult α) :
    InputStatus.classify .Final result ⦃ outcome => outcome = Spec.completedResult result ⦄ := by
  cases result with
  | Ok pair => cases pair; simp [InputStatus.classify, Spec.completedResult, spec_ok]
  | Err error => cases error <;> simp [InputStatus.classify, Spec.completedResult, spec_ok]

/-- The default complete entry point preserves a final-input contract. -/
theorem complete_spec {P α : Type} (pi : DirectParser P α) (parser : P)
    (input : Slice U8) (cursor : Cursor) (contract : Spec.ParseResult α → Prop)
    (hp : pi.parse_with parser input cursor ParseContext.FINAL ⦃ outcome => Spec.completed contract outcome ⦄) :
    DirectParser.parse pi parser input cursor ⦃ result => contract result ⦄ := by
  unfold DirectParser.parse
  step with hp as ⟨outcome, houtcome⟩
  rcases houtcome with ⟨result, hresult, rfl⟩
  cases result with
  | Err error => simpa [Spec.completedResult, ParseOutcome.into_complete, spec_ok] using hresult
  | Ok pair =>
    rcases pair with ⟨next, value⟩
    simpa [Spec.completedResult, ParseOutcome.into_complete, spec_ok] using hresult

theorem bit_spec (input : Slice U8) (cursor : Cursor) :
    Bit.Insts.RusthammerParserInputBool.parse_with () input cursor ParseContext.FINAL
      ⦃ result => Spec.completed (Spec.bitOutcome input cursor) result ⦄ := by
  rw [Bit.Insts.RusthammerParserInputBool.parse_with_eq]
  simp only [ParseContext.FINAL, Order.DEFAULT]
  have hp : read_bit_ordered input cursor .HighFirst ⦃ result => Spec.bitOutcome input cursor result ⦄ := by
    by_cases h : cursor.bit.val < 8 ∧ cursor.byte.val < input.val.length
    · simpa only [read_bit, Spec.bitOutcome, if_pos h] using read_bit_success input cursor h.1 h.2
    · simpa only [read_bit, Spec.bitOutcome, if_neg h] using read_bit_failure input cursor h
  step with hp as ⟨result, hresult⟩
  step with classify_final_spec result as ⟨outcome, houtcome⟩
  exact ⟨result, hresult, houtcome⟩

theorem bits_spec (parser : Bits) (input : Slice U8) (cursor : Cursor)
    (hconfig : Spec.validBits parser) :
    Bits.Insts.RusthammerParserInputU64.parse_with parser input cursor ParseContext.FINAL
      ⦃ result => Spec.completed (Spec.bitsOutcome input cursor parser.width) result ⦄ := by
  rw [Bits.Insts.RusthammerParserInputU64.parse_with_eq]
  simp only [ParseContext.FINAL, Order.DEFAULT, read_ordered_bits]
  step with read_bits_spec input cursor parser hconfig as ⟨result, hresult⟩
  step with classify_final_spec result as ⟨outcome, houtcome⟩
  exact ⟨result, hresult, houtcome⟩

theorem take_aligned_parser_spec (parser : TakeAligned) (input : Slice U8) (cursor : Cursor) :
    TakeAligned.Insts.RusthammerParserInputSharedInputSliceU8.parse_with parser input cursor ParseContext.FINAL
      ⦃ result => Spec.completed (Spec.takeAlignedOutcome input cursor parser.count) result ⦄ := by
  rw [TakeAligned.Insts.RusthammerParserInputSharedInputSliceU8.parse_with_eq]
  simp only [ParseContext.FINAL]
  step with take_aligned_spec input cursor parser.count as ⟨result, hresult⟩
  step with classify_final_spec result as ⟨outcome, houtcome⟩
  exact ⟨result, hresult, houtcome⟩

/-- Final-input sequencing retains the earlier complete-buffer relation. -/
theorem seq_spec {P Q α β : Type} (pi : DirectParser P α) (qi : DirectParser Q β)
    (parser : Seq P Q) (input : Slice U8) (cursor : Cursor)
    (first : Cursor → Spec.ParseResult α → Prop)
    (second : Cursor → Spec.ParseResult β → Prop)
    (hp : ∀ start, pi.parse_with parser.first input start ParseContext.FINAL
      ⦃ result => Spec.completed (first start) result ⦄)
    (hq : ∀ start, qi.parse_with parser.second input start ParseContext.FINAL
      ⦃ result => Spec.completed (second start) result ⦄) :
    Seq.Insts.RusthammerParserInputPair.parse_with pi qi parser input cursor ParseContext.FINAL
      ⦃ result => Spec.completed (Spec.sequence first second cursor) result ⦄ := by
  rw [Seq.Insts.RusthammerParserInputPair.parse_with_eq]
  step with hp cursor as ⟨outcome, houtcome⟩
  rcases houtcome with ⟨left, hleft, rfl⟩
  cases left with
  | Err error =>
    simp only [Spec.completedResult, spec_ok, Spec.completed_error]
    exact ⟨.Err error, hleft, rfl⟩
  | Ok pair =>
    rcases pair with ⟨middle, a⟩
    simp only [Spec.completedResult]
    step with hq middle as ⟨outcome, houtcome⟩
    rcases houtcome with ⟨right, hright, rfl⟩
    cases right with
    | Err error =>
      simp only [Spec.completedResult, spec_ok, Spec.completed_error]
      exact ⟨.Ok (middle, a), hleft, .Err error, hright, rfl⟩
    | Ok pair =>
      rcases pair with ⟨last, b⟩
      simp only [Spec.completedResult, spec_ok, Spec.completed_success]
      exact ⟨.Ok (middle, a), hleft, .Ok (last, b), hright, rfl⟩

theorem map_spec {P F α β : Type} (pi : DirectParser P α) (fi : core.ops.function.Fn F α β)
    (parser : Map P F) (input : Slice U8) (cursor : Cursor)
    (child : Cursor → Spec.ParseResult α → Prop) (mapping : α → β → Prop)
    (hp : pi.parse_with parser.parser input cursor ParseContext.FINAL
      ⦃ result => Spec.completed (child cursor) result ⦄)
    (hf : ∀ next value, child cursor (.Ok (next, value)) →
      fi.call parser.map value ⦃ result => mapping value result ⦄) :
    Map.Insts.RusthammerParser.parse_with pi fi parser input cursor ParseContext.FINAL
      ⦃ result => Spec.completed (Spec.map child mapping cursor) result ⦄ := by
  rw [Map.Insts.RusthammerParser.parse_with_eq]
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
    simp only [Spec.completed_success]
    exact ⟨.Ok (next, value), hparsed, mapped, hmapped, rfl⟩

theorem verify_spec {P F α : Type} (pi : DirectParser P α) (fi : core.ops.function.Fn F α Bool)
    (parser : Verify P F) (input : Slice U8) (cursor : Cursor)
    (child : Cursor → Spec.ParseResult α → Prop) (predicate : α → Prop)
    [DecidablePred predicate]
    (hp : pi.parse_with parser.parser input cursor ParseContext.FINAL
      ⦃ result => Spec.completed (child cursor) result ⦄)
    (hf : ∀ next value, child cursor (.Ok (next, value)) →
      fi.call parser.predicate value ⦃ result => result = decide (predicate value) ⦄) :
    Verify.Insts.RusthammerParser.parse_with pi fi parser input cursor ParseContext.FINAL
      ⦃ result => Spec.completed (Spec.verify child predicate cursor) result ⦄ := by
  rw [Verify.Insts.RusthammerParser.parse_with_eq]
  step with hp as ⟨outcome, houtcome⟩
  rcases houtcome with ⟨parsed, hparsed, rfl⟩
  cases parsed with
  | Err error =>
    simp only [Spec.completedResult, spec_ok, Spec.completed_error]
    exact ⟨.Err error, hparsed, rfl⟩
  | Ok pair =>
    rcases pair with ⟨next, value⟩
    simp only [Spec.completedResult]
    step with hf next value hparsed as ⟨accepted, haccepted⟩
    by_cases hpred : predicate value
    · have htrue : accepted = true := by simpa [hpred] using haccepted
      simp only [htrue, ↓reduceIte, spec_ok, Spec.completed_success]
      exact ⟨.Ok (next, value), hparsed, by simp [hpred]⟩
    · have hfalse : accepted = false := by simpa [hpred] using haccepted
      simp only [hfalse, Bool.false_eq_true, ↓reduceIte, spec_ok, Spec.completed_error]
      exact ⟨.Ok (next, value), hparsed, by simp [hpred]⟩

end RustHammer.Proofs
