import RustHammer.RepeatProofs

open Aeneas Aeneas.Std Result WP

namespace RustHammer.Proofs
open Code

/-- Unbounded repetition terminates by strictly decreasing the mathematical
number of remaining input bits. It enforces valid, advancing child cursors at
runtime, and handles the count limit before arithmetic or vector growth. -/
theorem repeat_unbounded_with_spec {P α : Type} (pi : Parser P α) (parser : P) (min : Usize)
    (input : Slice U8) (cursor : Cursor) (status : InputStatus)
    (child : Cursor → ParseOutcome α → Prop)
    (hp : ∀ start, pi.parse_with parser input start status ⦃ result => child start result ⦄) :
    Repeat.Insts.RusthammerParserInputVec.parse_with pi { parser, bounds := { min, max := none } }
      input cursor status ⦃ result => Spec.unboundedRepeat input child min.val cursor result ⦄ := by
  unfold Repeat.Insts.RusthammerParserInputVec.parse_with
  step with repeat_run_unbounded_spec pi (Collect.Insts.RusthammerRepeatAccumulatorAVec α)
    parser min () input cursor status child (fun values state => state.val = values) hp
    (by simp [Collect.Insts.RusthammerRepeatAccumulatorAVec.init, spec_ok])
    (by
      intro values next after value state _ _ hlen hstate
      simp only [Collect.Insts.RusthammerRepeatAccumulatorAVec.step]
      step with alloc.vec.Vec.push_spec state value (by simpa only [hstate] using hlen) as ⟨appended, happended⟩
      simpa [hstate] using happended) as ⟨outcome, houtcome⟩
  exact (accumulated_collection _ outcome).mp houtcome

theorem repeat_unbounded_final_spec {P α : Type} (pi : Parser P α) (parser : P) (min : Usize)
    (input : Slice U8) (cursor : Cursor) (child : Cursor → Spec.ParseResult α → Prop)
    (hp : ∀ start, pi.parse_with parser input start .Final
      ⦃ result => Spec.completed (child start) result ⦄) :
    Repeat.Insts.RusthammerParserInputVec.parse_with pi { parser, bounds := { min, max := none } }
      input cursor .Final
      ⦃ result => Spec.completed (Spec.unboundedRepeatComplete input child min.val cursor) result ⦄ := by
  step with repeat_unbounded_with_spec pi parser min input cursor .Final
    (fun start => Spec.completed (child start)) hp as ⟨outcome, houtcome⟩
  cases outcome with
  | Success next values => exact ⟨.Ok (next, values), houtcome, rfl⟩
  | Error error => exact ⟨.Err error, houtcome, rfl⟩
  | NeedMore =>
    by_cases hv : Spec.validCursor input cursor
    · simp only [Spec.unboundedRepeat, Spec.collectedValues, Spec.unboundedRepetition, if_pos hv] at houtcome
      rcases houtcome with ⟨_, _, _, _, parsed, _, heq⟩
      cases parsed with
      | Err _ => cases heq
      | Ok pair => cases pair; cases heq
    · simp [Spec.unboundedRepeat, Spec.collectedValues, Spec.unboundedRepetition, hv] at houtcome

theorem repeat_unbounded_spec {P α : Type} (pi : Parser P α) (parser : P) (min : Usize)
    (input : Slice U8) (cursor : Cursor) (child : Cursor → Spec.ParseResult α → Prop)
    (hp : ∀ start, pi.parse_with parser input start .Final
      ⦃ result => Spec.completed (child start) result ⦄) :
    Parser.parse.default (Repeat.Insts.RusthammerParserInputVec pi)
      { parser, bounds := { min, max := none } } input cursor
      ⦃ result => Spec.unboundedRepeatComplete input child min.val cursor result ⦄ := by
  exact complete_spec (Repeat.Insts.RusthammerParserInputVec pi)
    { parser, bounds := { min, max := none } } input cursor
    (Spec.unboundedRepeatComplete input child min.val cursor)
    (repeat_unbounded_final_spec pi parser min input cursor child hp)

/-- Invalid initial cursors are rejected without any child-parser assumptions. -/
theorem repeat_unbounded_invalid_cursor {P α : Type} (pi : Parser P α) (parser : P) (min : Usize)
    (input : Slice U8) (cursor : Cursor) (status : InputStatus)
    (hcursor : ¬Spec.validCursor input cursor) :
    Repeat.Insts.RusthammerParserInputVec.parse_with pi { parser, bounds := { min, max := none } }
      input cursor status ⦃ result => result = .Error .InvalidCursor ⦄ := by
  unfold Repeat.Insts.RusthammerParserInputVec.parse_with repeat_run repeat_run_with
  simp only [core.option.Option.is_none, Option.isNone]
  step with repeat_start_spec input cursor true as ⟨initial, hinitial⟩
  simp [hcursor] at hinitial
  simp [hinitial, spec_ok]

/-- Each retained unbounded item consumes at least one bit; unit outputs count too. -/
theorem advancing_repetitions_consumption {α : Type} (input : Slice U8)
    (child : Cursor → ParseOutcome α → Prop) (cursor next : Cursor) (values : List α)
    (h : Spec.repetitions (Spec.advancing input child) cursor values next) :
    Spec.position cursor + values.length ≤ Spec.position next := by
  induction h with
  | empty => simp
  | append hprefix hlast ih =>
    have hstep := hlast.2.2
    simp only [List.length_append, List.length_singleton]
    omega

theorem repeat_unbounded_success_properties {α : Type} (input : Slice U8)
    (child : Cursor → ParseOutcome α → Prop) (min : Nat)
    (cursor next : Cursor) (values : alloc.vec.Vec α)
    (h : Spec.unboundedRepeat input child min cursor (.Success next values)) :
    min ≤ values.val.length ∧ Spec.position cursor + values.val.length ≤ Spec.position next := by
  by_cases hv : Spec.validCursor input cursor
  · simp only [Spec.unboundedRepeat, Spec.collectedValues, Spec.unboundedRepetition, if_pos hv] at h
    exact ⟨h.1, advancing_repetitions_consumption input child cursor next values.val h.2.1⟩
  · simp [Spec.unboundedRepeat, Spec.collectedValues, Spec.unboundedRepetition, hv] at h

theorem repeat_unbounded_bits_with_spec (parser : Bits) (min : Usize) (input : Slice U8)
    (cursor : Cursor) (status : InputStatus) (hconfig : Spec.validBits parser) :
    Repeat.Insts.RusthammerParserInputVec.parse_with Bits.Insts.RusthammerParserInputU64
      { parser, bounds := { min, max := none } } input cursor status
      ⦃ result => Spec.unboundedRepeat input
        (fun start => Partial.primitive status (Spec.bitsOutcome input start parser.width))
        min.val cursor result ⦄ := by
  exact repeat_unbounded_with_spec Bits.Insts.RusthammerParserInputU64 parser min input cursor status
    _ (fun start => bits_with_spec parser input start status hconfig)

theorem repeat_unbounded_payloads_with_spec (parser : TakeAligned) (min : Usize) (input : Slice U8)
    (cursor : Cursor) (status : InputStatus) :
    Repeat.Insts.RusthammerParserInputVec.parse_with
      TakeAligned.Insts.RusthammerParserInputSharedInputSliceU8 { parser, bounds := { min, max := none } }
      input cursor status ⦃ result => Spec.unboundedRepeat input
        (fun start => Partial.primitive status (Spec.takeAlignedOutcome input start parser.count))
        min.val cursor result ⦄ := by
  exact repeat_unbounded_with_spec TakeAligned.Insts.RusthammerParserInputSharedInputSliceU8
    parser min input cursor status _ (fun start => take_aligned_with_spec parser input start status)

end RustHammer.Proofs
