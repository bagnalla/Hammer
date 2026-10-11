import RustHammer.RepeatProofs

open RustHammer.Code.grammar.bytes
  RustHammer.Code.grammar.numeric
  RustHammer.Code.grammar.repeat
  RustHammer.Code.input_types

open Aeneas Aeneas.Std Result WP

namespace RustHammer.Proofs
open Code

/-- Unbounded repetition terminates by strictly decreasing the mathematical
number of remaining input bits. It enforces valid, advancing child cursors at
runtime, and handles the count limit before arithmetic or vector growth. -/
theorem repeat_unbounded_with_spec {P α : Type} (pi : parser_traits.Parser P α) (parser : P) (min : Usize)
    (input : Slice U8) (cursor : Cursor) (context : ByteOrder)
    (child : Cursor → Spec.ParseResult α → Prop)
    (hp : ∀ start, pi.parse_with parser input start context ⦃ result => child start result ⦄) :
    Repeat.Insts.RusthammerParser_traitsParserInputVec.parse_with pi { parser, bounds := { min, max := none } }
      input cursor context ⦃ result => Spec.unboundedRepeat input child min.val cursor result ⦄ := by
  rw [Repeat.Insts.RusthammerParser_traitsParserInputVec.parse_with]
  step with repeat_run_unbounded_spec pi (Collect.Insts.RusthammerGrammarRepeatRepeatAccumulatorAVec α)
    parser min () input cursor context child (fun values state => state.val = values) hp
    (by simp [Collect.Insts.RusthammerGrammarRepeatRepeatAccumulatorAVec.init, spec_ok])
    (by
      intro values next after value state _ _ hlen hstate
      simp only [Collect.Insts.RusthammerGrammarRepeatRepeatAccumulatorAVec.step]
      step with alloc.vec.Vec.push_spec state value (by simpa only [hstate] using hlen) as ⟨appended, happended⟩
      simpa [hstate] using happended) as ⟨outcome, houtcome⟩
  exact (accumulated_collection _ outcome).mp houtcome

theorem repeat_unbounded_final_spec {P α : Type} (pi : parser_traits.Parser P α) (parser : P) (min : Usize)
    (input : Slice U8) (cursor : Cursor) (child : Cursor → Spec.ParseResult α → Prop)
    (hp : ∀ start, pi.parse_with parser input start ByteOrder.Big
      ⦃ result => Spec.satisfies (child start) result ⦄) :
    Repeat.Insts.RusthammerParser_traitsParserInputVec.parse_with pi { parser, bounds := { min, max := none } }
      input cursor ByteOrder.Big
      ⦃ result => Spec.satisfies (Spec.unboundedRepeatComplete input child min.val cursor) result ⦄ := by
  step with repeat_unbounded_with_spec pi parser min input cursor ByteOrder.Big
    (fun start => Spec.satisfies (child start)) hp as ⟨outcome, houtcome⟩
  cases outcome with
  | Ok pair =>
    rcases pair with ⟨next, values⟩
    exact ⟨.Ok (next, values), houtcome, rfl⟩
  | Err error => exact ⟨.Err error, houtcome, rfl⟩
theorem repeat_unbounded_spec {P α : Type} (pi : parser_traits.Parser P α) (parser : P) (min : Usize)
    (input : Slice U8) (cursor : Cursor) (child : Cursor → Spec.ParseResult α → Prop)
    (hp : ∀ start, pi.parse_with parser input start ByteOrder.Big
      ⦃ result => Spec.satisfies (child start) result ⦄) :
    parser_traits.Parser.parse.default (Repeat.Insts.RusthammerParser_traitsParserInputVec pi)
      { parser, bounds := { min, max := none } } input cursor
      ⦃ result => Spec.unboundedRepeatComplete input child min.val cursor result ⦄ := by
  exact complete_spec (Repeat.Insts.RusthammerParser_traitsParserInputVec pi)
    { parser, bounds := { min, max := none } } input cursor
    (Spec.unboundedRepeatComplete input child min.val cursor)
    (repeat_unbounded_final_spec pi parser min input cursor child hp)

/-- Invalid initial cursors are rejected without any child-parser assumptions. -/
theorem repeat_unbounded_invalid_cursor {P α : Type} (pi : parser_traits.Parser P α) (parser : P) (min : Usize)
    (input : Slice U8) (cursor : Cursor) (context : ByteOrder)
    (hcursor : ¬Spec.validCursor input cursor) :
    Repeat.Insts.RusthammerParser_traitsParserInputVec.parse_with pi { parser, bounds := { min, max := none } }
      input cursor context ⦃ result => result = .Err .InvalidCursor ⦄ := by
  rw [Repeat.Insts.RusthammerParser_traitsParserInputVec.parse_with, grammar.repeat.repeat_run, grammar.repeat.repeat_run_with]
  simp only [core.option.Option.is_none, Option.isNone]
  step with repeat_start_spec input cursor true as ⟨initial, hinitial⟩
  simp [hcursor] at hinitial
  simp [hinitial, spec_ok]

/-- Each retained unbounded item consumes at least one bit; unit outputs count too. -/
theorem advancing_repetitions_consumption {α : Type} (input : Slice U8)
    (child : Cursor → Spec.ParseResult α → Prop) (cursor next : Cursor) (values : List α)
    (h : Spec.repetitions (Spec.advancing input child) cursor values next) :
    Spec.position cursor + values.length ≤ Spec.position next := by
  induction h with
  | empty => simp
  | append hprefix hlast ih =>
    have hstep := hlast.2.2
    simp only [List.length_append, List.length_singleton]
    omega

theorem repeat_unbounded_success_properties {α : Type} (input : Slice U8)
    (child : Cursor → Spec.ParseResult α → Prop) (min : Nat)
    (cursor next : Cursor) (values : alloc.vec.Vec α)
    (h : Spec.unboundedRepeat input child min cursor (.Ok (next, values))) :
    min ≤ values.val.length ∧ Spec.position cursor + values.val.length ≤ Spec.position next := by
  by_cases hv : Spec.validCursor input cursor
  · simp only [Spec.unboundedRepeat, Spec.collectedValues, Spec.unboundedRepetition, if_pos hv] at h
    exact ⟨h.1, advancing_repetitions_consumption input child cursor next values.val h.2.1⟩
  · simp [Spec.unboundedRepeat, Spec.collectedValues, Spec.unboundedRepetition, hv] at h

theorem repeat_unbounded_bits_with_spec (parser : Bits) (min : Usize) (input : Slice U8)
    (cursor : Cursor) (hconfig : Spec.validBits parser) :
    Repeat.Insts.RusthammerParser_traitsParserInputVec.parse_with Bits.Insts.RusthammerParser_traitsParserInputU64
      { parser, bounds := { min, max := none } } input cursor ByteOrder.Big
      ⦃ result => Spec.unboundedRepeat input
        (fun start => Contracts.primitive (Spec.bitsOutcome input start parser.width))
        min.val cursor result ⦄ := by
  exact repeat_unbounded_with_spec Bits.Insts.RusthammerParser_traitsParserInputU64 parser min input cursor ByteOrder.Big
    _ (fun start => bits_with_spec parser input start hconfig)

theorem repeat_unbounded_payloads_with_spec (parser : TakeAligned) (min : Usize) (input : Slice U8)
    (cursor : Cursor) :
    Repeat.Insts.RusthammerParser_traitsParserInputVec.parse_with
      TakeAligned.Insts.RusthammerParser_traitsParserInputSharedInputSliceU8 { parser, bounds := { min, max := none } }
      input cursor ByteOrder.Big ⦃ result => Spec.unboundedRepeat input
        (fun start => Contracts.primitive (Spec.takeAlignedOutcome input start parser.count))
        min.val cursor result ⦄ := by
  exact repeat_unbounded_with_spec TakeAligned.Insts.RusthammerParser_traitsParserInputSharedInputSliceU8
    parser min input cursor ByteOrder.Big _ (fun start => take_aligned_with_spec parser input start)

end RustHammer.Proofs
