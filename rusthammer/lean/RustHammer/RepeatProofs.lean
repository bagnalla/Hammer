import RustHammer.RepeatSpec
import RustHammer.RepeatSupport

open Aeneas Aeneas.Std Result WP

namespace RustHammer.Proofs
open Code

theorem repeat_new_spec {P : Type} (parser : P) (min max : Usize) :
    Repeat.new parser min max ⦃ result => Spec.repeatNewOutcome parser min max result ⦄ := by
  by_cases hbounds : min.val ≤ max.val
  · have h : ¬min > max := by scalar_tac
    simp [Repeat.new, Spec.repeatNewOutcome, hbounds, h, spec_ok]
  · have h : min > max := by scalar_tac
    simp [Repeat.new, Spec.repeatNewOutcome, hbounds, h, spec_ok]

theorem repeat_new_valid {P : Type} (child : P) (min max : Usize) (parser : Repeat P)
    (hnew : Repeat.new child min max = ok (.Ok parser)) : Spec.validRepeat parser := by
  have hspec := repeat_new_spec child min max
  rw [hnew] at hspec
  simp only [spec_ok, Spec.repeatNewOutcome] at hspec
  split at hspec
  · cases hspec
    simpa [Spec.validRepeat] using (show min.val ≤ max.val from ‹_›)
  · cases hspec

theorem repeat_exact_spec {P : Type} (parser : P) (count : Usize) :
    Repeat.exact parser count ⦃ result =>
      result = { parser, min := count, max := some count } ∧ Spec.validRepeat result ⦄ := by
  simp [Repeat.exact, Spec.validRepeat, spec_ok]

theorem repeat_at_least_spec {P : Type} (parser : P) (min : Usize) :
    Repeat.at_least parser min ⦃ result =>
      result = { parser, min, max := none } ∧ Spec.validRepeat result ⦄ := by
  simp [Repeat.at_least, Spec.validRepeat, spec_ok]

theorem repeat_min_spec {P : Type} (parser : Repeat P) :
    Repeat.impl.min parser ⦃ result => result = parser.min ⦄ := by
  simp [Repeat.impl.min, spec_ok]

theorem repeat_max_spec {P : Type} (parser : Repeat P) :
    Repeat.impl.max parser ⦃ result => result = parser.max ⦄ := by
  simp [Repeat.impl.max, spec_ok]

/-- Finite repetition terminates by the number of remaining permitted calls,
including empty successes. This proves bounds, stopping, rollback, and all three
outcomes under the child contract, without depending on an allocation strategy. -/
theorem repeat_with_spec {P α : Type} (pi : Parser P α) (parser : Repeat P)
    (max : Usize) (hmax : parser.max = some max)
    (input : Slice U8) (cursor : Cursor) (status : InputStatus)
    (hconfig : Spec.validRepeat parser) (child : Cursor → ParseOutcome α → Prop)
    (hp : ∀ start, pi.parse_with parser.parser input start status ⦃ result => child start result ⦄) :
    Repeat.Insts.RusthammerParserInputVec.parse_with pi parser input cursor status
      ⦃ result => Spec.boundedRepeat child parser.min.val max.val cursor result ⦄ := by
  have hbounds := hconfig max hmax
  unfold Repeat.Insts.RusthammerParserInputVec.parse_with
  simp only [hmax, core.option.Option.is_none, Option.isNone, repeat_start, Bool.false_eq_true, ↓reduceIte,
    bind_ok]
  unfold Repeat.Insts.RusthammerParserInputVec.parse_with_loop
  apply loop.spec_decr_nat (fun state => max.val - state.2.2.val)
    (fun (values, next, count) => values.val.length = count.val ∧
      count.val ≤ max.val ∧ Spec.repetitions child cursor values.val next)
  · rintro ⟨values, next, count⟩ ⟨hcount, hbound, hprefix⟩
    unfold Repeat.Insts.RusthammerParserInputVec.parse_with_loop.body
    simp only [repeat_below_max, bind_ok, decide_eq_true_eq]
    by_cases hmore : count < max
    · have hless : count.val < max.val := by scalar_tac
      simp only [hmore, ↓reduceIte]
      step with hp next as ⟨parsed, hparsed⟩
      cases parsed with
      | Success after value =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        step with repeat_next_count_success count (by scalar_tac) as ⟨incremented, following, heq, hfollowing⟩
        simp only [heq]
        step with alloc.vec.Vec.push_spec values value (by scalar_tac) as ⟨appended, happended⟩
        refine ⟨?_, ?_, ?_, ?_⟩
        · simp only [happended, List.length_append, List.length_singleton]
          omega
        · omega
        · rw [happended]
          exact Spec.repetitions.append hprefix hparsed
        · omega
      | Error error =>
        by_cases hmin : count >= parser.min
        · have hminimum : parser.min.val ≤ count.val := by scalar_tac
          simp only [hmin, ↓reduceIte]
          step with recoverable_spec error as ⟨recover, hrecover⟩
          by_cases hreject : Spec.recoverable error
          · have htrue : recover = true := by simpa [hreject] using hrecover
            simp only [htrue, ↓reduceIte, spec_ok]
            exact ⟨by omega, by omega, hprefix, Or.inr ⟨error, hreject, hparsed⟩⟩
          · have hfalse : recover = false := by simpa [hreject] using hrecover
            simp only [hfalse, Bool.false_eq_true, ↓reduceIte, spec_ok]
            exact ⟨values.val, next, by omega, hprefix, hparsed, Or.inr hreject⟩
        · have hbelow : count.val < parser.min.val := by scalar_tac
          simp only [hmin, ↓reduceIte, spec_ok]
          exact ⟨values.val, next, by omega, hprefix, hparsed, Or.inl (by omega)⟩
      | NeedMore => exact ⟨values.val, next, by omega, hprefix, hparsed⟩
    · have heq : count.val = max.val := by scalar_tac
      simp only [hmore, ↓reduceIte, spec_ok]
      exact ⟨by simpa [hcount, heq] using hbounds, by omega, hprefix, Or.inl (by omega)⟩
  · exact ⟨by simp, by scalar_tac, Spec.repetitions.empty cursor⟩

theorem repeat_success_bounds {α : Type} (child : Cursor → ParseOutcome α → Prop)
    (min max : Nat) (cursor next : Cursor) (values : alloc.vec.Vec α)
    (h : Spec.boundedRepeat child min max cursor (.Success next values)) :
    min ≤ values.val.length ∧ values.val.length ≤ max := ⟨h.1, h.2.1⟩

/-- Final-input child contracts rule out NeedMore for the whole repetition. -/
theorem repeat_final_spec {P α : Type} (pi : Parser P α) (parser : Repeat P)
    (max : Usize) (hmax : parser.max = some max)
    (input : Slice U8) (cursor : Cursor) (hconfig : Spec.validRepeat parser)
    (child : Cursor → Spec.ParseResult α → Prop)
    (hp : ∀ start, pi.parse_with parser.parser input start .Final
      ⦃ result => Spec.completed (child start) result ⦄) :
    Repeat.Insts.RusthammerParserInputVec.parse_with pi parser input cursor .Final
      ⦃ result => Spec.completed
        (Spec.boundedRepeatComplete child parser.min.val max.val cursor) result ⦄ := by
  step with repeat_with_spec pi parser max hmax input cursor .Final hconfig
    (fun start => Spec.completed (child start)) hp as ⟨outcome, houtcome⟩
  cases outcome with
  | Success next values => exact ⟨.Ok (next, values), houtcome, rfl⟩
  | Error error => exact ⟨.Err error, houtcome, rfl⟩
  | NeedMore =>
    rcases houtcome with ⟨_, _, _, _, parsed, _, heq⟩
    cases parsed with
    | Err _ => cases heq
    | Ok pair => cases pair; cases heq

theorem repeat_spec {P α : Type} (pi : Parser P α) (parser : Repeat P)
    (max : Usize) (hmax : parser.max = some max)
    (input : Slice U8) (cursor : Cursor) (hconfig : Spec.validRepeat parser)
    (child : Cursor → Spec.ParseResult α → Prop)
    (hp : ∀ start, pi.parse_with parser.parser input start .Final
      ⦃ result => Spec.completed (child start) result ⦄) :
    Parser.parse.default (Repeat.Insts.RusthammerParserInputVec pi) parser input cursor
      ⦃ result => Spec.boundedRepeatComplete child parser.min.val max.val cursor result ⦄ := by
  exact complete_spec (Repeat.Insts.RusthammerParserInputVec pi) parser input cursor
    (Spec.boundedRepeatComplete child parser.min.val max.val cursor)
    (repeat_final_spec pi parser max hmax input cursor hconfig child hp)

/-- Equal bounds give precisely the original independent exact-count contract. -/
theorem bounded_repeat_exact {α : Type} (child : Cursor → ParseOutcome α → Prop)
    (count : Nat) (cursor : Cursor) (outcome : ParseOutcome (alloc.vec.Vec α)) :
    Spec.boundedRepeat child count count cursor outcome ↔ Spec.repeatN child count cursor outcome := by
  cases outcome with
  | Success next values =>
    constructor
    · rintro ⟨hlower, hupper, hprefix, _⟩
      exact ⟨by omega, hprefix⟩
    · rintro ⟨heq, hprefix⟩
      exact ⟨by omega, by omega, hprefix, Or.inl heq⟩
  | Error error =>
    constructor
    · rintro ⟨values, next, hcount, hprefix, herror, _⟩
      exact ⟨values, next, hcount, hprefix, herror⟩
    · rintro ⟨values, next, hcount, hprefix, herror⟩
      exact ⟨values, next, hcount, hprefix, herror, Or.inl hcount⟩
  | NeedMore => rfl

/-- Exact repetition is a specialization of the shared implementation theorem. -/
theorem repeat_exact_with_spec {P α : Type} (pi : Parser P α) (parser : P) (count : Usize)
    (input : Slice U8) (cursor : Cursor) (status : InputStatus)
    (child : Cursor → ParseOutcome α → Prop)
    (hp : ∀ start, pi.parse_with parser input start status ⦃ result => child start result ⦄) :
    Repeat.Insts.RusthammerParserInputVec.parse_with pi { parser, min := count, max := some count }
      input cursor status ⦃ result => Spec.repeatN child count.val cursor result ⦄ := by
  step with repeat_with_spec pi { parser, min := count, max := some count } count rfl input cursor status
    (by simp [Spec.validRepeat]) child hp as ⟨outcome, houtcome⟩
  exact (bounded_repeat_exact child count.val cursor outcome).mp houtcome

theorem repeat_exact_success_length {α : Type} (child : Cursor → ParseOutcome α → Prop)
    (count : Nat) (cursor next : Cursor) (values : alloc.vec.Vec α)
    (h : Spec.repeatN child count cursor (.Success next values)) :
    values.val.length = count := h.1

theorem repeat_exact_final_spec {P α : Type} (pi : Parser P α) (parser : P) (count : Usize)
    (input : Slice U8) (cursor : Cursor) (child : Cursor → Spec.ParseResult α → Prop)
    (hp : ∀ start, pi.parse_with parser input start .Final
      ⦃ result => Spec.completed (child start) result ⦄) :
    Repeat.Insts.RusthammerParserInputVec.parse_with pi { parser, min := count, max := some count }
      input cursor .Final
      ⦃ result => Spec.completed (Spec.repeatNComplete child count.val cursor) result ⦄ := by
  step with repeat_exact_with_spec pi parser count input cursor .Final
    (fun start => Spec.completed (child start)) hp as ⟨outcome, houtcome⟩
  cases outcome with
  | Success next values => exact ⟨.Ok (next, values), houtcome, rfl⟩
  | Error error => exact ⟨.Err error, houtcome, rfl⟩
  | NeedMore =>
    rcases houtcome with ⟨_, _, _, _, parsed, _, heq⟩
    cases parsed with
    | Err _ => cases heq
    | Ok pair => cases pair; cases heq

theorem repeat_exact_complete_spec {P α : Type} (pi : Parser P α) (parser : P) (count : Usize)
    (input : Slice U8) (cursor : Cursor) (child : Cursor → Spec.ParseResult α → Prop)
    (hp : ∀ start, pi.parse_with parser input start .Final
      ⦃ result => Spec.completed (child start) result ⦄) :
    Parser.parse.default (Repeat.Insts.RusthammerParserInputVec pi)
      { parser, min := count, max := some count } input cursor
      ⦃ result => Spec.repeatNComplete child count.val cursor result ⦄ := by
  exact complete_spec (Repeat.Insts.RusthammerParserInputVec pi)
    { parser, min := count, max := some count } input cursor
    (Spec.repeatNComplete child count.val cursor)
    (repeat_exact_final_spec pi parser count input cursor child hp)

/-- Zero maximum requires no correctness or termination assumption about the child. -/
theorem repeat_zero {P α : Type} (pi : Parser P α) (parser : P)
    (input : Slice U8) (cursor : Cursor) (status : InputStatus) :
    Repeat.Insts.RusthammerParserInputVec.parse_with pi { parser, min := 0#usize, max := some 0#usize }
      input cursor status ⦃ result => result = .Success cursor (alloc.vec.Vec.new α) ⦄ := by
  unfold Repeat.Insts.RusthammerParserInputVec.parse_with
  simp only [core.option.Option.is_none, Option.isNone, repeat_start, Bool.false_eq_true,
    ↓reduceIte, bind_ok]
  unfold Repeat.Insts.RusthammerParserInputVec.parse_with_loop loop
  simp [Repeat.Insts.RusthammerParserInputVec.parse_with_loop.body, repeat_below_max, spec_ok]

/-- A first error below the minimum or a fatal error needs no later-call contracts. -/
theorem repeat_first_error {P α : Type} (pi : Parser P α) (parser : Repeat P)
    (max : Usize) (hmax : parser.max = some max)
    (input : Slice U8) (cursor : Cursor) (status : InputStatus) (error : ParseError)
    (hpositive : max.val > 0) (hstop : parser.min.val > 0 ∨ ¬Spec.recoverable error)
    (hp : pi.parse_with parser.parser input cursor status ⦃ result => result = .Error error ⦄) :
    Repeat.Insts.RusthammerParserInputVec.parse_with pi parser input cursor status
      ⦃ result => result = .Error error ⦄ := by
  have hmore : 0#usize < max := by scalar_tac
  unfold Repeat.Insts.RusthammerParserInputVec.parse_with
  simp only [hmax, core.option.Option.is_none, Option.isNone, repeat_start, Bool.false_eq_true, ↓reduceIte,
    bind_ok]
  unfold Repeat.Insts.RusthammerParserInputVec.parse_with_loop loop
  simp only [Repeat.Insts.RusthammerParserInputVec.parse_with_loop.body, repeat_below_max,
    bind_ok, hmore, decide_true, ↓reduceIte]
  step with hp as ⟨result, hresult⟩
  simp only [hresult]
  by_cases hmin : 0#usize >= parser.min
  · have hzero : parser.min.val = 0 := by scalar_tac
    have hfatal : ¬Spec.recoverable error := hstop.resolve_left (by omega)
    simp only [hmin, ↓reduceIte]
    step with recoverable_spec error as ⟨recover, hrecover⟩
    have hfalse : recover = false := by simpa [hfatal] using hrecover
    simp [hfalse, spec_ok]
  · simp [hmin, spec_ok]

theorem repeat_first_need_more {P α : Type} (pi : Parser P α) (parser : Repeat P)
    (max : Usize) (hmax : parser.max = some max)
    (input : Slice U8) (cursor : Cursor) (status : InputStatus)
    (hpositive : max.val > 0)
    (hp : pi.parse_with parser.parser input cursor status ⦃ result => result = .NeedMore ⦄) :
    Repeat.Insts.RusthammerParserInputVec.parse_with pi parser input cursor status
      ⦃ result => result = .NeedMore ⦄ := by
  have hmore : 0#usize < max := by scalar_tac
  unfold Repeat.Insts.RusthammerParserInputVec.parse_with
  simp only [hmax, core.option.Option.is_none, Option.isNone, repeat_start, Bool.false_eq_true, ↓reduceIte,
    bind_ok]
  unfold Repeat.Insts.RusthammerParserInputVec.parse_with_loop loop
  simp only [Repeat.Insts.RusthammerParserInputVec.parse_with_loop.body, repeat_below_max,
    bind_ok, hmore, decide_true, ↓reduceIte]
  step with hp as ⟨result, hresult⟩
  simp [hresult, spec_ok]

/-- Repeating fixed-width children adds their consumption, including width zero. -/
theorem repetitions_advance {α : Type} (child : Cursor → ParseOutcome α → Prop)
    (width : Nat) (cursor next : Cursor) (values : List α)
    (hp : ∀ start after value, child start (.Success after value) →
      Spec.position after = Spec.position start + width)
    (h : Spec.repetitions child cursor values next) :
    Spec.position next = Spec.position cursor + values.length * width := by
  induction h with
  | empty => simp
  | append hprefix hlast ih =>
    have hstep := hp _ _ _ hlast
    simp only [List.length_append, List.length_singleton, Nat.add_mul, Nat.one_mul]
    omega

/-- Numeric fields instantiate the generic bounded contract in both input modes. -/
theorem repeat_bits_with_spec (parser : Bits) (min max : Usize) (input : Slice U8)
    (cursor : Cursor) (status : InputStatus) (hconfig : Spec.validBits parser)
    (hbounds : min.val ≤ max.val) :
    Repeat.Insts.RusthammerParserInputVec.parse_with Bits.Insts.RusthammerParserInputU64
      { parser, min, max := some max } input cursor status
      ⦃ result => Spec.boundedRepeat
        (fun start => Partial.primitive status (Spec.bitsOutcome input start parser.width))
        min.val max.val cursor result ⦄ := by
  exact repeat_with_spec Bits.Insts.RusthammerParserInputU64 { parser, min, max := some max } max rfl input cursor status
    (by simpa [Spec.validRepeat] using hbounds) _ (fun start => bits_with_spec parser input start status hconfig)

/-- Borrowed outputs use the same theorem without Copy or Clone assumptions. -/
theorem repeat_payloads_with_spec (parser : TakeAligned) (min max : Usize) (input : Slice U8)
    (cursor : Cursor) (status : InputStatus) (hbounds : min.val ≤ max.val) :
    Repeat.Insts.RusthammerParserInputVec.parse_with
      TakeAligned.Insts.RusthammerParserInputSharedInputSliceU8 { parser, min, max := some max } input cursor status
      ⦃ result => Spec.boundedRepeat
        (fun start => Partial.primitive status (Spec.takeAlignedOutcome input start parser.count))
        min.val max.val cursor result ⦄ := by
  exact repeat_with_spec TakeAligned.Insts.RusthammerParserInputSharedInputSliceU8
    { parser, min, max := some max } max rfl input cursor status (by simpa [Spec.validRepeat] using hbounds) _
    (fun start => take_aligned_with_spec parser input start status)

end RustHammer.Proofs
