import RustHammer.ControlProofs
import RustHammer.PartialSpec

open Aeneas Aeneas.Std Result WP

namespace RustHammer.Proofs
open Code

theorem classify_spec {α : Type} (status : InputStatus) (result : Spec.ParseResult α) :
    InputStatus.classify status result ⦃ outcome => outcome = Partial.primitiveResult status result ⦄ := by
  cases result with
  | Ok pair => cases pair; cases status <;> simp [InputStatus.classify, Partial.primitiveResult, Spec.completedResult, spec_ok]
  | Err error => cases error <;> cases status <;> simp [InputStatus.classify, Partial.primitiveResult, Spec.completedResult, spec_ok]

theorem bit_with_spec (input : Slice U8) (cursor : Cursor) (status : InputStatus) :
    Bit.Insts.RusthammerParserInputBool.parse_with () input cursor (Spec.defaultContext status)
      ⦃ result => Partial.primitive status (Spec.bitOutcome input cursor) result ⦄ := by
  rw [Bit.Insts.RusthammerParserInputBool.parse_with_eq]
  simp only [Order.DEFAULT]
  have hp : read_bit_ordered input cursor .HighFirst ⦃ result => Spec.bitOutcome input cursor result ⦄ := by
    by_cases h : cursor.bit.val < 8 ∧ cursor.byte.val < input.val.length
    · simpa only [read_bit, Spec.bitOutcome, if_pos h] using read_bit_success input cursor h.1 h.2
    · simpa only [read_bit, Spec.bitOutcome, if_neg h] using read_bit_failure input cursor h
  step with hp as ⟨result, hresult⟩
  step with classify_spec status result as ⟨outcome, houtcome⟩
  exact ⟨result, hresult, houtcome⟩

theorem bits_with_spec (parser : Bits) (input : Slice U8) (cursor : Cursor) (status : InputStatus)
    (hconfig : Spec.validBits parser) :
    Bits.Insts.RusthammerParserInputU64.parse_with parser input cursor (Spec.defaultContext status)
      ⦃ result => Partial.primitive status (Spec.bitsOutcome input cursor parser.width) result ⦄ := by
  rw [Bits.Insts.RusthammerParserInputU64.parse_with_eq]
  simp only [Order.DEFAULT, read_ordered_bits]
  step with read_bits_spec input cursor parser hconfig as ⟨result, hresult⟩
  step with classify_spec status result as ⟨outcome, houtcome⟩
  exact ⟨result, hresult, houtcome⟩

theorem take_aligned_with_spec (parser : TakeAligned) (input : Slice U8) (cursor : Cursor)
    (status : InputStatus) :
    TakeAligned.Insts.RusthammerParserInputSharedInputSliceU8.parse_with parser input cursor (Spec.defaultContext status)
      ⦃ result => Partial.primitive status (Spec.takeAlignedOutcome input cursor parser.count) result ⦄ := by
  rw [TakeAligned.Insts.RusthammerParserInputSharedInputSliceU8.parse_with_eq]
  step with take_aligned_spec input cursor parser.count as ⟨result, hresult⟩
  step with classify_spec status result as ⟨outcome, houtcome⟩
  exact ⟨result, hresult, houtcome⟩

theorem literal_with_spec (parser : Literal) (input : Slice U8) (cursor : Cursor)
    (status : InputStatus) (hconfig : Spec.validLiteral parser) :
    Literal.Insts.RusthammerParserInputU64.parse_with parser input cursor (Spec.defaultContext status)
      ⦃ result => Partial.primitive status (Spec.literalOutcome input cursor parser.bits.width parser.value) result ⦄ := by
  rw [Literal.Insts.RusthammerParserInputU64.parse_with_eq]
  step with literal_decode_spec parser input cursor hconfig as ⟨result, hresult⟩
  step with classify_spec status result as ⟨outcome, houtcome⟩
  exact ⟨result, hresult, houtcome⟩

theorem seq_with_spec {P Q α β : Type} (pi : DirectParser P α) (qi : DirectParser Q β)
    (parser : Seq P Q) (input : Slice U8) (cursor : Cursor) (context : ParseContext)
    (first : Cursor → ParseOutcome α → Prop) (second : Cursor → ParseOutcome β → Prop)
    (hp : ∀ start, pi.parse_with parser.first input start context ⦃ result => first start result ⦄)
    (hq : ∀ start, qi.parse_with parser.second input start context ⦃ result => second start result ⦄) :
    Seq.Insts.RusthammerParserInputPair.parse_with pi qi parser input cursor context
      ⦃ result => Partial.sequence first second cursor result ⦄ := by
  rw [Seq.Insts.RusthammerParserInputPair.parse_with_eq]
  step with hp cursor as ⟨left, hleft⟩
  cases left with
  | NeedMore => simp only [spec_ok]; exact ⟨.NeedMore, hleft, rfl⟩
  | Error error => simp only [spec_ok]; exact ⟨.Error error, hleft, rfl⟩
  | Success middle a =>
    step with hq middle as ⟨right, hright⟩
    cases right with
    | NeedMore => simp only [spec_ok]; exact ⟨.Success middle a, hleft, .NeedMore, hright, rfl⟩
    | Error error => simp only [spec_ok]; exact ⟨.Success middle a, hleft, .Error error, hright, rfl⟩
    | Success last b => simp only [spec_ok]; exact ⟨.Success middle a, hleft, .Success last b, hright, rfl⟩

theorem map_with_spec {P F α β : Type} (pi : DirectParser P α) (fi : core.ops.function.Fn F α β)
    (parser : Map P F) (input : Slice U8) (cursor : Cursor) (context : ParseContext)
    (child : Cursor → ParseOutcome α → Prop) (mapping : α → β → Prop)
    (hp : pi.parse_with parser.parser input cursor context ⦃ result => child cursor result ⦄)
    (hf : ∀ next value, child cursor (.Success next value) →
      fi.call parser.map value ⦃ result => mapping value result ⦄) :
    Map.Insts.RusthammerParser.parse_with pi fi parser input cursor context
      ⦃ result => Partial.map child mapping cursor result ⦄ := by
  rw [Map.Insts.RusthammerParser.parse_with_eq]
  step with hp as ⟨parsed, hparsed⟩
  cases parsed with
  | NeedMore => simp only [spec_ok]; exact ⟨.NeedMore, hparsed, rfl⟩
  | Error error => simp only [spec_ok]; exact ⟨.Error error, hparsed, rfl⟩
  | Success next value =>
    step with hf next value hparsed as ⟨mapped, hmapped⟩
    exact ⟨.Success next value, hparsed, mapped, hmapped, rfl⟩

theorem verify_with_spec {P F α : Type} (pi : DirectParser P α) (fi : core.ops.function.Fn F α Bool)
    (parser : Verify P F) (input : Slice U8) (cursor : Cursor) (context : ParseContext)
    (child : Cursor → ParseOutcome α → Prop) (predicate : α → Prop) [DecidablePred predicate]
    (hp : pi.parse_with parser.parser input cursor context ⦃ result => child cursor result ⦄)
    (hf : ∀ next value, child cursor (.Success next value) →
      fi.call parser.predicate value ⦃ result => result = decide (predicate value) ⦄) :
    Verify.Insts.RusthammerParser.parse_with pi fi parser input cursor context
      ⦃ result => Partial.verify child predicate cursor result ⦄ := by
  rw [Verify.Insts.RusthammerParser.parse_with_eq]
  step with hp as ⟨parsed, hparsed⟩
  cases parsed with
  | NeedMore => simp only [spec_ok]; exact ⟨.NeedMore, hparsed, rfl⟩
  | Error error => simp only [spec_ok]; exact ⟨.Error error, hparsed, rfl⟩
  | Success next value =>
    step with hf next value hparsed as ⟨accepted, haccepted⟩
    by_cases hpred : predicate value
    · have htrue : accepted = true := by simpa [hpred] using haccepted
      simp only [htrue, ↓reduceIte, spec_ok]
      exact ⟨.Success next value, hparsed, by simp [hpred]⟩
    · have hfalse : accepted = false := by simpa [hpred] using haccepted
      simp only [hfalse, Bool.false_eq_true, ↓reduceIte, spec_ok]
      exact ⟨.Success next value, hparsed, by simp [hpred]⟩

theorem choice_with_spec {P Q α : Type} (pi : DirectParser P α) (qi : DirectParser Q α)
    (parser : Choice P Q) (input : Slice U8) (cursor : Cursor) (context : ParseContext)
    (first second : Cursor → ParseOutcome α → Prop)
    (hp : ∀ start, pi.parse_with parser.first input start context ⦃ result => first start result ⦄)
    (hq : ∀ start, qi.parse_with parser.second input start context ⦃ result => second start result ⦄) :
    Choice.Insts.RusthammerParser.parse_with pi qi parser input cursor context
      ⦃ result => Partial.choice first second cursor result ⦄ := by
  rw [Choice.Insts.RusthammerParser.parse_with_eq]
  step with hp cursor as ⟨left, hleft⟩
  cases left with
  | NeedMore => simp only [spec_ok]; exact ⟨.NeedMore, hleft, rfl⟩
  | Success next value => simp only [spec_ok]; exact ⟨.Success next value, hleft, rfl⟩
  | Error error =>
    step with recoverable_spec error as ⟨recover, hrecover⟩
    by_cases h : Spec.recoverable error
    · have htrue : recover = true := by simpa [h] using hrecover
      simp only [htrue, ↓reduceIte]
      step with hq cursor as ⟨right, hright⟩
      exact ⟨.Error error, hleft, by simpa only [if_pos h] using hright⟩
    · have hfalse : recover = false := by simpa [h] using hrecover
      simp only [hfalse, Bool.false_eq_true, ↓reduceIte, spec_ok]
      exact ⟨.Error error, hleft, by simp [h]⟩

/-- End rejects all remaining bits and malformed cursors, without consuming input. -/
theorem end_with_spec (input : Slice U8) (cursor : Cursor) (status : InputStatus) :
    End.Insts.RusthammerParserInputTuple.parse_with () input cursor (Spec.defaultContext status)
      ⦃ result => Partial.endOutcome input cursor status result ⦄ := by
  unfold Partial.endOutcome
  by_cases hvalid : Spec.validCursor input cursor
  · have hparts := hvalid
    unfold Spec.validCursor Spec.position at hparts
    have hbit : ¬cursor.bit ≥ 8#u8 := by scalar_tac
    have hbyte : ¬cursor.byte > input.len := by scalar_tac
    simp only [Spec.endOutcome, if_pos hvalid,
      End.Insts.RusthammerParserInputTuple.parse_with_eq, hbit, hbyte, ↓reduceIte]
    by_cases heq : cursor.byte = input.len
    · have hzero : cursor.bit = 0#u8 := by scalar_tac
      have hend : Spec.position cursor = 8 * input.val.length := by
        unfold Spec.position
        scalar_tac
      cases status <;> simp [heq, hzero, hend, spec_ok, Partial.endResult]
    · have hnotend : ¬Spec.position cursor = 8 * input.val.length := by
        unfold Spec.position
        scalar_tac
      simp [heq, hnotend, spec_ok, Partial.endResult]
  · have hparts := hvalid
    unfold Spec.validCursor Spec.position at hparts
    simp only [Spec.endOutcome, if_neg hvalid]
    by_cases hbit : cursor.bit ≥ 8#u8
    · simp [End.Insts.RusthammerParserInputTuple.parse_with_eq, hbit, spec_ok, Partial.endResult]
    · by_cases hbyte : cursor.byte > input.len
      · simp [End.Insts.RusthammerParserInputTuple.parse_with_eq, hbit, hbyte, spec_ok, Partial.endResult]
      · have heq : cursor.byte = input.len := by scalar_tac
        have hnonzero : cursor.bit ≠ 0#u8 := by scalar_tac
        simp [End.Insts.RusthammerParserInputTuple.parse_with_eq, hbit, heq, hnonzero, spec_ok, Partial.endResult]

theorem optional_with_spec {P α : Type} (pi : DirectParser P α) (parser : Optional P)
    (input : Slice U8) (cursor : Cursor) (context : ParseContext)
    (child : Cursor → ParseOutcome α → Prop)
    (hp : pi.parse_with parser.parser input cursor context ⦃ result => child cursor result ⦄) :
    Optional.Insts.RusthammerParserInputOption.parse_with pi parser input cursor context
      ⦃ result => Partial.optional child cursor result ⦄ := by
  rw [Optional.Insts.RusthammerParserInputOption.parse_with_eq]
  step with hp as ⟨parsed, hparsed⟩
  cases parsed with
  | NeedMore => simp only [spec_ok]; exact ⟨.NeedMore, hparsed, rfl⟩
  | Success next value => simp only [spec_ok]; exact ⟨.Success next value, hparsed, rfl⟩
  | Error error =>
    step with recoverable_spec error as ⟨recover, hrecover⟩
    by_cases h : Spec.recoverable error
    · have htrue : recover = true := by simpa [h] using hrecover
      simp only [htrue, ↓reduceIte, spec_ok]
      exact ⟨.Error error, hparsed, by simp [h]⟩
    · have hfalse : recover = false := by simpa [h] using hrecover
      simp only [hfalse, Bool.false_eq_true, ↓reduceIte, spec_ok]
      exact ⟨.Error error, hparsed, by simp [h]⟩

theorem and_with_spec {P α : Type} (pi : DirectParser P α) (parser : Code.And P)
    (input : Slice U8) (cursor : Cursor) (context : ParseContext)
    (child : Cursor → ParseOutcome α → Prop)
    (hp : pi.parse_with parser.parser input cursor context ⦃ result => child cursor result ⦄) :
    Code.And.Insts.RusthammerParserInputTuple.parse_with pi parser input cursor context
      ⦃ result => Partial.and child cursor result ⦄ := by
  rw [Code.And.Insts.RusthammerParserInputTuple.parse_with_eq]
  step with hp as ⟨parsed, hparsed⟩
  cases parsed with
  | NeedMore => simp only [spec_ok]; exact ⟨.NeedMore, hparsed, rfl⟩
  | Error error => simp only [spec_ok]; exact ⟨.Error error, hparsed, rfl⟩
  | Success next value => simp only [spec_ok]; exact ⟨.Success next value, hparsed, rfl⟩

theorem not_with_spec {P α : Type} (pi : DirectParser P α) (parser : Code.Not P)
    (input : Slice U8) (cursor : Cursor) (context : ParseContext)
    (child : Cursor → ParseOutcome α → Prop)
    (hp : pi.parse_with parser.parser input cursor context ⦃ result => child cursor result ⦄) :
    Code.Not.Insts.RusthammerParserInputTuple.parse_with pi parser input cursor context
      ⦃ result => Partial.not child cursor result ⦄ := by
  rw [Code.Not.Insts.RusthammerParserInputTuple.parse_with_eq]
  step with hp as ⟨parsed, hparsed⟩
  cases parsed with
  | NeedMore => simp only [spec_ok]; exact ⟨.NeedMore, hparsed, rfl⟩
  | Success next value => simp only [spec_ok]; exact ⟨.Success next value, hparsed, rfl⟩
  | Error error =>
    step with recoverable_spec error as ⟨recover, hrecover⟩
    by_cases h : Spec.recoverable error
    · have htrue : recover = true := by simpa [h] using hrecover
      simp only [htrue, ↓reduceIte, spec_ok]
      exact ⟨.Error error, hparsed, by simp [h]⟩
    · have hfalse : recover = false := by simpa [h] using hrecover
      simp only [hfalse, Bool.false_eq_true, ↓reduceIte, spec_ok]
      exact ⟨.Error error, hparsed, by simp [h]⟩

/-- No assumption about the second parser is required when the first needs input. -/
theorem choice_first_need_more {P Q α : Type} (pi : DirectParser P α) (qi : DirectParser Q α)
    (parser : Choice P Q) (input : Slice U8) (cursor : Cursor) (context : ParseContext)
    (hp : pi.parse_with parser.first input cursor context ⦃ result => result = .NeedMore ⦄) :
    Choice.Insts.RusthammerParser.parse_with pi qi parser input cursor context
      ⦃ result => result = .NeedMore ⦄ := by
  rw [Choice.Insts.RusthammerParser.parse_with_eq]
  step with hp as ⟨parsed, hparsed⟩
  simp [hparsed, spec_ok]

theorem seq_first_need_more {P Q α β : Type} (pi : DirectParser P α) (qi : DirectParser Q β)
    (parser : Seq P Q) (input : Slice U8) (cursor : Cursor) (context : ParseContext)
    (hp : pi.parse_with parser.first input cursor context ⦃ result => result = .NeedMore ⦄) :
    Seq.Insts.RusthammerParserInputPair.parse_with pi qi parser input cursor context
      ⦃ result => result = .NeedMore ⦄ := by
  rw [Seq.Insts.RusthammerParserInputPair.parse_with_eq]
  step with hp as ⟨parsed, hparsed⟩
  simp [hparsed, spec_ok]

theorem map_need_more {P F α β : Type} (pi : DirectParser P α) (fi : core.ops.function.Fn F α β)
    (parser : Map P F) (input : Slice U8) (cursor : Cursor) (context : ParseContext)
    (hp : pi.parse_with parser.parser input cursor context ⦃ result => result = .NeedMore ⦄) :
    Map.Insts.RusthammerParser.parse_with pi fi parser input cursor context
      ⦃ result => result = .NeedMore ⦄ := by
  rw [Map.Insts.RusthammerParser.parse_with_eq]
  step with hp as ⟨parsed, hparsed⟩
  simp [hparsed, spec_ok]

theorem verify_need_more {P F α : Type} (pi : DirectParser P α) (fi : core.ops.function.Fn F α Bool)
    (parser : Verify P F) (input : Slice U8) (cursor : Cursor) (context : ParseContext)
    (hp : pi.parse_with parser.parser input cursor context ⦃ result => result = .NeedMore ⦄) :
    Verify.Insts.RusthammerParser.parse_with pi fi parser input cursor context
      ⦃ result => result = .NeedMore ⦄ := by
  rw [Verify.Insts.RusthammerParser.parse_with_eq]
  step with hp as ⟨parsed, hparsed⟩
  simp [hparsed, spec_ok]

theorem map_child_error {P F α β : Type} (pi : DirectParser P α) (fi : core.ops.function.Fn F α β)
    (parser : Map P F) (context : ParseContext) (input : Slice U8) (cursor : Cursor) (error : ParseError)
    (hp : pi.parse_with parser.parser input cursor context ⦃ result => result = .Error error ⦄) :
    Map.Insts.RusthammerParser.parse_with pi fi parser input cursor context
      ⦃ result => result = .Error error ⦄ := by
  rw [Map.Insts.RusthammerParser.parse_with_eq]
  step with hp as ⟨parsed, hparsed⟩
  simp [hparsed, spec_ok]

theorem verify_child_error {P F α : Type} (pi : DirectParser P α)
    (fi : core.ops.function.Fn F α Bool) (parser : Verify P F)
    (context : ParseContext) (input : Slice U8) (cursor : Cursor) (error : ParseError)
    (hp : pi.parse_with parser.parser input cursor context ⦃ result => result = .Error error ⦄) :
    Verify.Insts.RusthammerParser.parse_with pi fi parser input cursor context
      ⦃ result => result = .Error error ⦄ := by
  rw [Verify.Insts.RusthammerParser.parse_with_eq]
  step with hp as ⟨parsed, hparsed⟩
  simp [hparsed, spec_ok]

theorem choice_first_success {P Q α : Type} (pi : DirectParser P α) (qi : DirectParser Q α)
    (parser : Choice P Q) (context : ParseContext) (input : Slice U8) (cursor next : Cursor) (value : α)
    (hp : pi.parse_with parser.first input cursor context ⦃ result => result = .Success next value ⦄) :
    Choice.Insts.RusthammerParser.parse_with pi qi parser input cursor context
      ⦃ result => result = .Success next value ⦄ := by
  rw [Choice.Insts.RusthammerParser.parse_with_eq]
  step with hp as ⟨left, hleft⟩
  simp [hleft, spec_ok]

theorem choice_first_fatal {P Q α : Type} (pi : DirectParser P α) (qi : DirectParser Q α)
    (parser : Choice P Q) (context : ParseContext) (input : Slice U8) (cursor : Cursor) (error : ParseError)
    (hfatal : ¬Spec.recoverable error)
    (hp : pi.parse_with parser.first input cursor context ⦃ result => result = .Error error ⦄) :
    Choice.Insts.RusthammerParser.parse_with pi qi parser input cursor context
      ⦃ result => result = .Error error ⦄ := by
  rw [Choice.Insts.RusthammerParser.parse_with_eq]
  step with hp as ⟨left, hleft⟩
  simp only [hleft]
  step with recoverable_spec error as ⟨retry, hretry⟩
  have hfalse : retry = false := by simpa [hfatal] using hretry
  simp [hfalse, spec_ok]

end RustHammer.Proofs
