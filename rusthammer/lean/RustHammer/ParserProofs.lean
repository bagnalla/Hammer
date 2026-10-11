import RustHammer.ControlProofs
import RustHammer.ParserSpec

open RustHammer.Code.grammar.bytes
  RustHammer.Code.grammar.control
  RustHammer.Code.grammar.numeric
  RustHammer.Code.grammar.position
  RustHammer.Code.grammar.sequence
  RustHammer.Code.grammar.transform
  RustHammer.Code.input_types

open Aeneas Aeneas.Std Result WP

namespace RustHammer.Proofs
open Code

theorem bit_with_spec (input : Slice U8) (cursor : Cursor) :
    Bit.Insts.RusthammerParser_traitsParserInputBool.parse_with () input cursor ByteOrder.Big
      ⦃ result => Contracts.primitive (Spec.bitOutcome input cursor) result ⦄ := by
  simpa only [Contracts.primitive, Spec.satisfies] using bit_spec input cursor

theorem bits_with_spec (parser : Bits) (input : Slice U8) (cursor : Cursor)
    (hconfig : Spec.validBits parser) :
    Bits.Insts.RusthammerParser_traitsParserInputU64.parse_with parser input cursor ByteOrder.Big
      ⦃ result => Contracts.primitive (Spec.bitsOutcome input cursor parser.width) result ⦄ := by
  simpa only [Contracts.primitive, Spec.satisfies] using bits_spec parser input cursor hconfig

theorem take_aligned_with_spec (parser : TakeAligned) (input : Slice U8) (cursor : Cursor) :
    TakeAligned.Insts.RusthammerParser_traitsParserInputSharedInputSliceU8.parse_with parser input cursor ByteOrder.Big
      ⦃ result => Contracts.primitive (Spec.takeAlignedOutcome input cursor parser.count) result ⦄ := by
  simpa only [Contracts.primitive, Spec.satisfies] using take_aligned_parser_spec parser input cursor

theorem literal_with_spec (parser : Literal) (input : Slice U8) (cursor : Cursor) (hconfig : Spec.validLiteral parser) :
    Literal.Insts.RusthammerParser_traitsParserInputU64.parse_with parser input cursor ByteOrder.Big
      ⦃ result => Contracts.primitive (Spec.literalOutcome input cursor parser.bits.width parser.value) result ⦄ := by
  simpa only [Contracts.primitive, Spec.satisfies] using literal_spec parser input cursor hconfig

theorem seq_with_spec {P Q α β : Type} (pi : parser_traits.Parser P α) (qi : parser_traits.Parser Q β)
    (parser : Seq P Q) (input : Slice U8) (cursor : Cursor) (context : ByteOrder)
    (first : Cursor → Spec.ParseResult α → Prop) (second : Cursor → Spec.ParseResult β → Prop)
    (hp : ∀ start, pi.parse_with parser.first input start context ⦃ result => first start result ⦄)
    (hq : ∀ start, qi.parse_with parser.second input start context ⦃ result => second start result ⦄) :
    Seq.Insts.RusthammerParser_traitsParserInputPair.parse_with pi qi parser input cursor context
      ⦃ result => Contracts.sequence first second cursor result ⦄ := by
  rw [Seq.Insts.RusthammerParser_traitsParserInputPair.parse_with]
  step with hp cursor as ⟨left, hleft⟩
  cases left with
  | Err error => simp only [spec_ok]; exact ⟨.Err error, hleft, rfl⟩
  | Ok pair =>
    rcases pair with ⟨middle, a⟩
    step with hq middle as ⟨right, hright⟩
    cases right with
    | Err error => simp only [spec_ok]; exact ⟨.Ok (middle, a), hleft, .Err error, hright, rfl⟩
    | Ok pair =>
      rcases pair with ⟨last, b⟩
      simp only []; exact ⟨.Ok (middle, a), hleft, .Ok (last, b), hright, rfl⟩

theorem map_with_spec {P F α β : Type} (pi : parser_traits.Parser P α) (fi : core.ops.function.Fn F α β)
    (parser : Map P F) (input : Slice U8) (cursor : Cursor) (context : ByteOrder)
    (child : Cursor → Spec.ParseResult α → Prop) (mapping : α → β → Prop)
    (hp : pi.parse_with parser.parser input cursor context ⦃ result => child cursor result ⦄)
    (hf : ∀ next value, child cursor (.Ok (next, value)) →
      fi.call parser.map value ⦃ result => mapping value result ⦄) :
    Map.Insts.RusthammerParser_traitsParser.parse_with pi fi parser input cursor context
      ⦃ result => Contracts.map child mapping cursor result ⦄ := by
  rw [Map.Insts.RusthammerParser_traitsParser.parse_with]
  step with hp as ⟨parsed, hparsed⟩
  cases parsed with
  | Err error => simp only [spec_ok]; exact ⟨.Err error, hparsed, rfl⟩
  | Ok pair =>
    rcases pair with ⟨next, value⟩
    step with hf next value hparsed as ⟨mapped, hmapped⟩
    exact ⟨.Ok (next, value), hparsed, mapped, hmapped, rfl⟩

theorem verify_with_spec {P F α : Type} (pi : parser_traits.Parser P α) (fi : core.ops.function.Fn F α Bool)
    (parser : Verify P F) (input : Slice U8) (cursor : Cursor) (context : ByteOrder)
    (child : Cursor → Spec.ParseResult α → Prop) (predicate : α → Prop) [DecidablePred predicate]
    (hp : pi.parse_with parser.parser input cursor context ⦃ result => child cursor result ⦄)
    (hf : ∀ next value, child cursor (.Ok (next, value)) →
      fi.call parser.predicate value ⦃ result => result = decide (predicate value) ⦄) :
    Verify.Insts.RusthammerParser_traitsParser.parse_with pi fi parser input cursor context
      ⦃ result => Contracts.verify child predicate cursor result ⦄ := by
  rw [Verify.Insts.RusthammerParser_traitsParser.parse_with]
  step with hp as ⟨parsed, hparsed⟩
  cases parsed with
  | Err error => simp only [spec_ok]; exact ⟨.Err error, hparsed, rfl⟩
  | Ok pair =>
    rcases pair with ⟨next, value⟩
    step with hf next value hparsed as ⟨accepted, haccepted⟩
    by_cases hpred : predicate value
    · have htrue : accepted = true := by simpa [hpred] using haccepted
      simp only [htrue, ↓reduceIte, spec_ok]
      exact ⟨.Ok (next, value), hparsed, by simp [hpred]⟩
    · have hfalse : accepted = false := by simpa [hpred] using haccepted
      simp only [hfalse, Bool.false_eq_true, ↓reduceIte, spec_ok]
      exact ⟨.Ok (next, value), hparsed, by simp [hpred]⟩

theorem choice_with_spec {P Q α : Type} (pi : parser_traits.Parser P α) (qi : parser_traits.Parser Q α)
    (parser : Choice P Q) (input : Slice U8) (cursor : Cursor) (context : ByteOrder)
    (first second : Cursor → Spec.ParseResult α → Prop)
    (hp : ∀ start, pi.parse_with parser.first input start context ⦃ result => first start result ⦄)
    (hq : ∀ start, qi.parse_with parser.second input start context ⦃ result => second start result ⦄) :
    Choice.Insts.RusthammerParser_traitsParser.parse_with pi qi parser input cursor context
      ⦃ result => Contracts.choice first second cursor result ⦄ := by
  rw [Choice.Insts.RusthammerParser_traitsParser.parse_with]
  step with hp cursor as ⟨left, hleft⟩
  cases left with
  | Ok pair =>
    rcases pair with ⟨next, value⟩
    simp only [spec_ok]; exact ⟨.Ok (next, value), hleft, rfl⟩
  | Err error =>
    step with recoverable_spec error as ⟨recover, hrecover⟩
    by_cases h : Spec.recoverable error
    · have htrue : recover = true := by simpa [h] using hrecover
      simp only [htrue, ↓reduceIte]
      step with hq cursor as ⟨right, hright⟩
      exact ⟨.Err error, hleft, by simpa only [if_pos h] using hright⟩
    · have hfalse : recover = false := by simpa [h] using hrecover
      simp only [hfalse, Bool.false_eq_true, ↓reduceIte, spec_ok]
      exact ⟨.Err error, hleft, by simp [h]⟩

/-- End rejects all remaining bits and malformed cursors, without consuming input. -/
theorem end_with_spec (input : Slice U8) (cursor : Cursor) :
    End.Insts.RusthammerParser_traitsParserInputTuple.parse_with () input cursor ByteOrder.Big
      ⦃ result => Contracts.endOutcome input cursor result ⦄ := by
  simpa only [Contracts.endOutcome, Spec.satisfies] using end_spec input cursor

theorem optional_with_spec {P α : Type} (pi : parser_traits.Parser P α) (parser : Optional P)
    (input : Slice U8) (cursor : Cursor) (context : ByteOrder)
    (child : Cursor → Spec.ParseResult α → Prop)
    (hp : pi.parse_with parser.parser input cursor context ⦃ result => child cursor result ⦄) :
    Optional.Insts.RusthammerParser_traitsParserInputOption.parse_with pi parser input cursor context
      ⦃ result => Contracts.optional child cursor result ⦄ := by
  rw [Optional.Insts.RusthammerParser_traitsParserInputOption.parse_with]
  step with hp as ⟨parsed, hparsed⟩
  cases parsed with
  | Ok pair =>
    rcases pair with ⟨next, value⟩
    simp only []; exact ⟨.Ok (next, value), hparsed, rfl⟩
  | Err error =>
    step with recoverable_spec error as ⟨recover, hrecover⟩
    by_cases h : Spec.recoverable error
    · have htrue : recover = true := by simpa [h] using hrecover
      simp only [htrue, ↓reduceIte, spec_ok]
      exact ⟨.Err error, hparsed, by simp [h]⟩
    · have hfalse : recover = false := by simpa [h] using hrecover
      simp only [hfalse, Bool.false_eq_true, ↓reduceIte, spec_ok]
      exact ⟨.Err error, hparsed, by simp [h]⟩

theorem and_with_spec {P α : Type} (pi : parser_traits.Parser P α) (parser : Code.grammar.control.And P)
    (input : Slice U8) (cursor : Cursor) (context : ByteOrder)
    (child : Cursor → Spec.ParseResult α → Prop)
    (hp : pi.parse_with parser.parser input cursor context ⦃ result => child cursor result ⦄) :
    Code.grammar.control.And.Insts.RusthammerParser_traitsParserInputTuple.parse_with pi parser input cursor context
      ⦃ result => Contracts.and child cursor result ⦄ := by
  rw [Code.grammar.control.And.Insts.RusthammerParser_traitsParserInputTuple.parse_with]
  step with hp as ⟨parsed, hparsed⟩
  cases parsed with
  | Err error => simp only [spec_ok]; exact ⟨.Err error, hparsed, rfl⟩
  | Ok pair =>
    rcases pair with ⟨next, value⟩
    simp only [spec_ok]; exact ⟨.Ok (next, value), hparsed, rfl⟩

theorem not_with_spec {P α : Type} (pi : parser_traits.Parser P α) (parser : Code.grammar.control.Not P)
    (input : Slice U8) (cursor : Cursor) (context : ByteOrder)
    (child : Cursor → Spec.ParseResult α → Prop)
    (hp : pi.parse_with parser.parser input cursor context ⦃ result => child cursor result ⦄) :
    Code.grammar.control.Not.Insts.RusthammerParser_traitsParserInputTuple.parse_with pi parser input cursor context
      ⦃ result => Contracts.not child cursor result ⦄ := by
  rw [Code.grammar.control.Not.Insts.RusthammerParser_traitsParserInputTuple.parse_with]
  step with hp as ⟨parsed, hparsed⟩
  cases parsed with
  | Ok pair =>
    rcases pair with ⟨next, value⟩
    simp only [spec_ok]; exact ⟨.Ok (next, value), hparsed, rfl⟩
  | Err error =>
    step with recoverable_spec error as ⟨recover, hrecover⟩
    by_cases h : Spec.recoverable error
    · have htrue : recover = true := by simpa [h] using hrecover
      simp only [htrue, ↓reduceIte, spec_ok]
      exact ⟨.Err error, hparsed, by simp [h]⟩
    · have hfalse : recover = false := by simpa [h] using hrecover
      simp only [hfalse, Bool.false_eq_true, ↓reduceIte, spec_ok]
      exact ⟨.Err error, hparsed, by simp [h]⟩

/-- No assumption about the second parser is required when the first needs input. -/

theorem map_child_error {P F α β : Type} (pi : parser_traits.Parser P α) (fi : core.ops.function.Fn F α β)
    (parser : Map P F) (context : ByteOrder) (input : Slice U8) (cursor : Cursor) (error : ParseError)
    (hp : pi.parse_with parser.parser input cursor context ⦃ result => result = .Err error ⦄) :
    Map.Insts.RusthammerParser_traitsParser.parse_with pi fi parser input cursor context
      ⦃ result => result = .Err error ⦄ := by
  rw [Map.Insts.RusthammerParser_traitsParser.parse_with]
  step with hp as ⟨parsed, hparsed⟩
  simp [hparsed, spec_ok]

theorem verify_child_error {P F α : Type} (pi : parser_traits.Parser P α)
    (fi : core.ops.function.Fn F α Bool) (parser : Verify P F)
    (context : ByteOrder) (input : Slice U8) (cursor : Cursor) (error : ParseError)
    (hp : pi.parse_with parser.parser input cursor context ⦃ result => result = .Err error ⦄) :
    Verify.Insts.RusthammerParser_traitsParser.parse_with pi fi parser input cursor context
      ⦃ result => result = .Err error ⦄ := by
  rw [Verify.Insts.RusthammerParser_traitsParser.parse_with]
  step with hp as ⟨parsed, hparsed⟩
  simp [hparsed, spec_ok]

theorem choice_first_success {P Q α : Type} (pi : parser_traits.Parser P α) (qi : parser_traits.Parser Q α)
    (parser : Choice P Q) (context : ByteOrder) (input : Slice U8) (cursor next : Cursor) (value : α)
    (hp : pi.parse_with parser.first input cursor context ⦃ result => result = .Ok (next, value) ⦄) :
    Choice.Insts.RusthammerParser_traitsParser.parse_with pi qi parser input cursor context
      ⦃ result => result = .Ok (next, value) ⦄ := by
  rw [Choice.Insts.RusthammerParser_traitsParser.parse_with]
  step with hp as ⟨left, hleft⟩
  simp [hleft, spec_ok]

theorem choice_first_fatal {P Q α : Type} (pi : parser_traits.Parser P α) (qi : parser_traits.Parser Q α)
    (parser : Choice P Q) (context : ByteOrder) (input : Slice U8) (cursor : Cursor) (error : ParseError)
    (hfatal : ¬Spec.recoverable error)
    (hp : pi.parse_with parser.first input cursor context ⦃ result => result = .Err error ⦄) :
    Choice.Insts.RusthammerParser_traitsParser.parse_with pi qi parser input cursor context
      ⦃ result => result = .Err error ⦄ := by
  rw [Choice.Insts.RusthammerParser_traitsParser.parse_with]
  step with hp as ⟨left, hleft⟩
  simp only [hleft]
  step with recoverable_spec error as ⟨retry, hretry⟩
  have hfalse : retry = false := by simpa [hfatal] using hretry
  simp [hfalse, spec_ok]

end RustHammer.Proofs
