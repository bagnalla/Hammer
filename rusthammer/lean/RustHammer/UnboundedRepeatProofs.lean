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
    Repeat.Insts.RusthammerParserInputVec.parse_with pi { parser, min, max := none }
      input cursor status ⦃ result => Spec.unboundedRepeat input child min.val cursor result ⦄ := by
  unfold Repeat.Insts.RusthammerParserInputVec.parse_with
  simp only [core.option.Option.is_none, Option.isNone]
  step with repeat_start_spec input cursor true as ⟨initial, hinitial⟩
  by_cases hvalid : Spec.validCursor input cursor
  · have hi : initial = .Ok () := by simpa [hvalid] using hinitial
    simp only [hi, Spec.unboundedRepeat, if_pos hvalid]
    unfold Repeat.Insts.RusthammerParserInputVec.parse_with_loop
    apply loop.spec_decr_nat (fun state => 8 * input.val.length - Spec.position state.2.1)
      (fun (values, next, count) => values.val.length = count.val ∧ Spec.validCursor input next ∧
        Spec.repetitions (Spec.advancing input child) cursor values.val next)
    · rintro ⟨values, next, count⟩ ⟨hcount, hnext, hprefix⟩
      unfold Repeat.Insts.RusthammerParserInputVec.parse_with_loop.body
      simp only [repeat_below_max, bind_ok, ↓reduceIte]
      step with hp next as ⟨parsed, hparsed⟩
      cases parsed with
      | Success after value =>
        step with repeat_progress_spec input next after hnext as ⟨progress, hprogress⟩
        by_cases hafter : Spec.validCursor input after
        · by_cases hforward : Spec.position next < Spec.position after
          · simp only [if_pos hafter, if_pos hforward] at hprogress
            simp only [hprogress]
            by_cases hroom : count.val < Usize.max
            · step with repeat_next_count_success count hroom as ⟨incremented, following, heq, hfollowing⟩
              simp only [heq]
              step with alloc.vec.Vec.push_spec values value (by omega) as ⟨appended, happended⟩
              refine ⟨?_, hafter.1, hafter.2, ?_, ?_⟩
              · simp only [happended, List.length_append, List.length_singleton]
                omega
              · rw [happended]
                exact Spec.repetitions.append hprefix ⟨hparsed, hafter, hforward⟩
              · have hbound := hafter.2
                omega
            · have hfull : count.val = Usize.max := by scalar_tac
              step with repeat_next_count_overflow count hfull as ⟨overflow, hoverflow⟩
              simp only [hoverflow, spec_ok]
              exact ⟨values.val, next, by scalar_tac, hprefix, Or.inr ⟨after, value, hparsed,
                Or.inr (Or.inr ⟨hafter, hforward, by omega, rfl⟩)⟩⟩
          · simp only [if_pos hafter, if_neg hforward] at hprogress
            simp only [hprogress, spec_ok]
            exact ⟨values.val, next, by scalar_tac, hprefix, Or.inr ⟨after, value, hparsed,
              Or.inr (Or.inl ⟨hafter, by omega, rfl⟩)⟩⟩
        · simp only [if_neg hafter] at hprogress
          simp only [hprogress, spec_ok]
          exact ⟨values.val, next, by scalar_tac, hprefix,
            Or.inr ⟨after, value, hparsed, Or.inl ⟨hafter, rfl⟩⟩⟩
      | Error error =>
        by_cases hmin : count >= min
        · have hminimum : min.val ≤ count.val := by scalar_tac
          simp only [hmin, ↓reduceIte]
          step with recoverable_spec error as ⟨recover, hrecover⟩
          by_cases hreject : Spec.recoverable error
          · have htrue : recover = true := by simpa [hreject] using hrecover
            simp only [htrue, ↓reduceIte, spec_ok]
            exact ⟨by omega, hprefix, error, hreject, hparsed⟩
          · have hfalse : recover = false := by simpa [hreject] using hrecover
            simp only [hfalse, Bool.false_eq_true, ↓reduceIte, spec_ok]
            exact ⟨values.val, next, by scalar_tac, hprefix, Or.inl ⟨hparsed, Or.inr hreject⟩⟩
        · have hbelow : count.val < min.val := by scalar_tac
          simp only [hmin, ↓reduceIte, spec_ok]
          exact ⟨values.val, next, by scalar_tac, hprefix, Or.inl ⟨hparsed, Or.inl (by omega)⟩⟩
      | NeedMore => exact ⟨values.val, next, by scalar_tac, hprefix, hparsed⟩
    · exact ⟨by simp, hvalid, Spec.repetitions.empty cursor⟩
  · simp [hvalid] at hinitial
    simp [hinitial, Spec.unboundedRepeat, hvalid, spec_ok]

theorem repeat_unbounded_final_spec {P α : Type} (pi : Parser P α) (parser : P) (min : Usize)
    (input : Slice U8) (cursor : Cursor) (child : Cursor → Spec.ParseResult α → Prop)
    (hp : ∀ start, pi.parse_with parser input start .Final
      ⦃ result => Spec.completed (child start) result ⦄) :
    Repeat.Insts.RusthammerParserInputVec.parse_with pi { parser, min, max := none }
      input cursor .Final
      ⦃ result => Spec.completed (Spec.unboundedRepeatComplete input child min.val cursor) result ⦄ := by
  step with repeat_unbounded_with_spec pi parser min input cursor .Final
    (fun start => Spec.completed (child start)) hp as ⟨outcome, houtcome⟩
  cases outcome with
  | Success next values => exact ⟨.Ok (next, values), houtcome, rfl⟩
  | Error error => exact ⟨.Err error, houtcome, rfl⟩
  | NeedMore =>
    by_cases hv : Spec.validCursor input cursor
    · simp only [Spec.unboundedRepeat, if_pos hv] at houtcome
      rcases houtcome with ⟨_, _, _, _, parsed, _, heq⟩
      cases parsed with
      | Err _ => cases heq
      | Ok pair => cases pair; cases heq
    · simp [Spec.unboundedRepeat, hv] at houtcome

theorem repeat_unbounded_spec {P α : Type} (pi : Parser P α) (parser : P) (min : Usize)
    (input : Slice U8) (cursor : Cursor) (child : Cursor → Spec.ParseResult α → Prop)
    (hp : ∀ start, pi.parse_with parser input start .Final
      ⦃ result => Spec.completed (child start) result ⦄) :
    Parser.parse.default (Repeat.Insts.RusthammerParserInputVec pi)
      { parser, min, max := none } input cursor
      ⦃ result => Spec.unboundedRepeatComplete input child min.val cursor result ⦄ := by
  exact complete_spec (Repeat.Insts.RusthammerParserInputVec pi)
    { parser, min, max := none } input cursor
    (Spec.unboundedRepeatComplete input child min.val cursor)
    (repeat_unbounded_final_spec pi parser min input cursor child hp)

/-- Invalid initial cursors are rejected without any child-parser assumptions. -/
theorem repeat_unbounded_invalid_cursor {P α : Type} (pi : Parser P α) (parser : P) (min : Usize)
    (input : Slice U8) (cursor : Cursor) (status : InputStatus)
    (hcursor : ¬Spec.validCursor input cursor) :
    Repeat.Insts.RusthammerParserInputVec.parse_with pi { parser, min, max := none }
      input cursor status ⦃ result => result = .Error .InvalidCursor ⦄ := by
  unfold Repeat.Insts.RusthammerParserInputVec.parse_with
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
  · simp only [Spec.unboundedRepeat, if_pos hv] at h
    exact ⟨h.1, advancing_repetitions_consumption input child cursor next values.val h.2.1⟩
  · simp [Spec.unboundedRepeat, hv] at h

theorem repeat_unbounded_bits_with_spec (parser : Bits) (min : Usize) (input : Slice U8)
    (cursor : Cursor) (status : InputStatus) (hconfig : Spec.validBits parser) :
    Repeat.Insts.RusthammerParserInputVec.parse_with Bits.Insts.RusthammerParserInputU64
      { parser, min, max := none } input cursor status
      ⦃ result => Spec.unboundedRepeat input
        (fun start => Partial.primitive status (Spec.bitsOutcome input start parser.width))
        min.val cursor result ⦄ := by
  exact repeat_unbounded_with_spec Bits.Insts.RusthammerParserInputU64 parser min input cursor status
    _ (fun start => bits_with_spec parser input start status hconfig)

theorem repeat_unbounded_payloads_with_spec (parser : TakeAligned) (min : Usize) (input : Slice U8)
    (cursor : Cursor) (status : InputStatus) :
    Repeat.Insts.RusthammerParserInputVec.parse_with
      TakeAligned.Insts.RusthammerParserInputSharedInputSliceU8 { parser, min, max := none }
      input cursor status ⦃ result => Spec.unboundedRepeat input
        (fun start => Partial.primitive status (Spec.takeAlignedOutcome input start parser.count))
        min.val cursor result ⦄ := by
  exact repeat_unbounded_with_spec TakeAligned.Insts.RusthammerParserInputSharedInputSliceU8
    parser min input cursor status _ (fun start => take_aligned_with_spec parser input start status)

end RustHammer.Proofs
