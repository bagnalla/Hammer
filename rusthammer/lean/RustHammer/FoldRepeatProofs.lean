import RustHammer.FoldRepeatSpec
import RustHammer.RepeatDriverProofs

open Aeneas Aeneas.Std Result WP

namespace RustHammer.Proofs
open Code

theorem fold_repeat_new_spec {P I F : Type} (parser : P) (min max : Usize) (init : I) (fold : F) :
    FoldRepeat.new parser min max init fold
      ⦃ result => Spec.foldRepeatNewOutcome parser min max init fold result ⦄ := by
  by_cases hbounds : min.val ≤ max.val
  · have h : ¬min > max := by scalar_tac
    simp [FoldRepeat.new, RepeatBounds.new, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      Spec.foldRepeatNewOutcome, hbounds, h, spec_ok]
  · have h : min > max := by scalar_tac
    simp [FoldRepeat.new, RepeatBounds.new, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      Spec.foldRepeatNewOutcome, hbounds, h, spec_ok]

theorem fold_repeat_new_valid {P I F : Type} (child : P) (min max : Usize) (init : I) (fold : F)
    (parser : FoldRepeat P I F) (hnew : FoldRepeat.new child min max init fold = ok (.Ok parser)) :
    Spec.validFoldRepeat parser := by
  have hspec := fold_repeat_new_spec child min max init fold
  rw [hnew] at hspec
  simp only [spec_ok, Spec.foldRepeatNewOutcome] at hspec
  split at hspec
  · cases hspec
    simpa [Spec.validFoldRepeat, Spec.validRepeatBounds] using (show min.val ≤ max.val from ‹_›)
  · cases hspec

theorem fold_repeat_exact_spec {P I F : Type} (parser : P) (count : Usize) (init : I) (fold : F) :
    FoldRepeat.exact parser count init fold ⦃ result =>
      result = { parser, bounds := { min := count, max := some count }, init, fold } ∧
      Spec.validFoldRepeat result ⦄ := by
  simp [FoldRepeat.exact, RepeatBounds.exact, Spec.validFoldRepeat, Spec.validRepeatBounds, spec_ok]

theorem fold_repeat_at_least_spec {P I F : Type} (parser : P) (min : Usize) (init : I) (fold : F) :
    FoldRepeat.at_least parser min init fold ⦃ result =>
      result = { parser, bounds := { min, max := none }, init, fold } ∧ Spec.validFoldRepeat result ⦄ := by
  simp [FoldRepeat.at_least, RepeatBounds.at_least, Spec.validFoldRepeat, Spec.validRepeatBounds, spec_ok]

theorem fold_repeat_min_spec {P I F : Type} (parser : FoldRepeat P I F) :
    FoldRepeat.min parser ⦃ result => result = parser.bounds.min ⦄ := by
  simp [FoldRepeat.min, spec_ok]

theorem fold_repeat_max_spec {P I F : Type} (parser : FoldRepeat P I F) :
    FoldRepeat.max parser ⦃ result => result = parser.bounds.max ⦄ := by
  simp [FoldRepeat.max, spec_ok]

/-- The public bounded fold implements the callback recurrence over exactly the
same child sequence, bounds, stopping, and rollback contract as collection. -/
theorem fold_repeat_with_spec {P I F α R : Type} (pi : Parser P α)
    (ii : core.ops.function.Fn I Unit R) (fi : core.ops.function.Fn F (R × α) R)
    (parser : FoldRepeat P I F) (max : Usize) (hmax : parser.bounds.max = some max)
    (input : Slice U8) (cursor : Cursor) (status : InputStatus) (hconfig : Spec.validFoldRepeat parser)
    (child : Cursor → ParseOutcome α → Prop) (initial : R → Prop) (fold : R → α → R → Prop)
    (hp : ∀ start, pi.parse_with parser.parser input start status ⦃ result => child start result ⦄)
    (hi : ii.call parser.init () ⦃ result => initial result ⦄)
    (hf : ∀ values next after value state,
      Spec.repetitions child cursor values next → child next (.Success after value) →
      values.length < max.val → Spec.folds initial fold values state →
      fi.call parser.fold (state, value) ⦃ result => fold state value result ⦄) :
    FoldRepeat.Insts.RusthammerParser.parse_with pi ii fi parser input cursor status
      ⦃ result => Spec.boundedFoldRepeat child initial fold parser.bounds.min.val max.val cursor result ⦄ := by
  have hb : parser.bounds = { min := parser.bounds.min, max := some max } := by
    cases h : parser.bounds; simp_all
  unfold FoldRepeat.Insts.RusthammerParser.parse_with
  rw [hb]
  apply repeat_run_bounded_spec pi (FoldRepeat.Insts.RusthammerRepeatAccumulator P ii fi)
    parser.parser parser.bounds.min max parser input cursor status (hconfig max hmax) child
    (Spec.folds initial fold) hp
  · simp only [FoldRepeat.Insts.RusthammerRepeatAccumulator.init]
    step with hi as ⟨state, hstate⟩
    exact Spec.folds.empty hstate
  · intro values next after value state hprefix hchild hlen hstate
    simp only [FoldRepeat.Insts.RusthammerRepeatAccumulator.step]
    step with hf values next after value state hprefix hchild hlen hstate as ⟨following, hfollowing⟩
    exact Spec.folds.append hstate hfollowing

/-- Unbounded folding retains only advancing successes and checks overflow before
calling the fold step. It uses the same input-based termination proof as collection. -/
theorem fold_repeat_unbounded_with_spec {P I F α R : Type} (pi : Parser P α)
    (ii : core.ops.function.Fn I Unit R) (fi : core.ops.function.Fn F (R × α) R)
    (parser : FoldRepeat P I F) (hmax : parser.bounds.max = none)
    (input : Slice U8) (cursor : Cursor) (status : InputStatus)
    (child : Cursor → ParseOutcome α → Prop) (initial : R → Prop) (fold : R → α → R → Prop)
    (hp : ∀ start, pi.parse_with parser.parser input start status ⦃ result => child start result ⦄)
    (hi : ii.call parser.init () ⦃ result => initial result ⦄)
    (hf : ∀ values next after value state,
      Spec.repetitions (Spec.advancing input child) cursor values next →
      Spec.advancing input child next (.Success after value) →
      values.length < Usize.max → Spec.folds initial fold values state →
      fi.call parser.fold (state, value) ⦃ result => fold state value result ⦄) :
    FoldRepeat.Insts.RusthammerParser.parse_with pi ii fi parser input cursor status
      ⦃ result => Spec.unboundedFoldRepeat input child initial fold parser.bounds.min.val cursor result ⦄ := by
  have hb : parser.bounds = { min := parser.bounds.min, max := none } := by
    cases h : parser.bounds; simp_all
  unfold FoldRepeat.Insts.RusthammerParser.parse_with
  rw [hb]
  apply repeat_run_unbounded_spec pi (FoldRepeat.Insts.RusthammerRepeatAccumulator P ii fi)
    parser.parser parser.bounds.min parser input cursor status child (Spec.folds initial fold) hp
  · simp only [FoldRepeat.Insts.RusthammerRepeatAccumulator.init]
    step with hi as ⟨state, hstate⟩
    exact Spec.folds.empty hstate
  · intro values next after value state hprefix hchild hlen hstate
    simp only [FoldRepeat.Insts.RusthammerRepeatAccumulator.step]
    step with hf values next after value state hprefix hchild hlen hstate as ⟨following, hfollowing⟩
    exact Spec.folds.append hstate hfollowing

/-- For deterministic callback contracts, this is an ordinary left fold. -/
theorem folds_function {α R : Type} (initial : R) (step : R → α → R) (values : List α) (state : R)
    (h : Spec.folds (fun r => r = initial) (fun r a result => result = step r a) values state) :
    state = values.foldl step initial := by
  induction h with
  | empty hi => exact hi
  | append _ hstep ih => simp [List.foldl_append, ← ih, hstep]

/-- Exact repetition folds precisely the configured number of child values. -/
theorem fold_repeat_exact_success {α R : Type} (child : Cursor → ParseOutcome α → Prop)
    (initial : R → Prop) (fold : R → α → R → Prop) (count : Nat) (cursor next : Cursor) (state : R)
    (h : Spec.boundedFoldRepeat child initial fold count count cursor (.Success next state)) :
    ∃ values, values.length = count ∧ Spec.repetitions child cursor values next ∧
      Spec.folds initial fold values state := by
  rcases h with ⟨values, hfold, hlo, hhi, hprefix, _⟩
  exact ⟨values, by omega, hprefix, hfold⟩

/-- Zero maximum needs only the initializer contract: neither child nor step runs. -/
theorem fold_repeat_zero {P I F α R : Type} (pi : Parser P α)
    (ii : core.ops.function.Fn I Unit R) (fi : core.ops.function.Fn F (R × α) R)
    (parser : P) (init : I) (fold : F) (input : Slice U8) (cursor : Cursor) (status : InputStatus)
    (initial : R → Prop) (hi : ii.call init () ⦃ result => initial result ⦄) :
    FoldRepeat.Insts.RusthammerParser.parse_with pi ii fi
      { parser, bounds := { min := 0#usize, max := some 0#usize }, init, fold } input cursor status
      ⦃ result => ∃ state, initial state ∧ result = .Success cursor state ⦄ := by
  unfold FoldRepeat.Insts.RusthammerParser.parse_with repeat_run repeat_run_with
  simp only [core.option.Option.is_none, Option.isNone, repeat_start, Bool.false_eq_true,
    ↓reduceIte, bind_ok, FoldRepeat.Insts.RusthammerRepeatAccumulator,
    FoldRepeat.Insts.RusthammerRepeatAccumulator.init]
  step with hi as ⟨state, hstate⟩
  unfold repeat_run_with_loop loop
  simp [repeat_run_with_loop.body, repeat_below_max, repeat_parse, spec_ok, hstate]

/-- Invalid unbounded input requires no child, initializer, or step contracts. -/
theorem fold_repeat_unbounded_invalid_cursor {P I F α R : Type} (pi : Parser P α)
    (ii : core.ops.function.Fn I Unit R) (fi : core.ops.function.Fn F (R × α) R)
    (parser : FoldRepeat P I F) (hmax : parser.bounds.max = none)
    (input : Slice U8) (cursor : Cursor) (status : InputStatus) (hc : ¬Spec.validCursor input cursor) :
    FoldRepeat.Insts.RusthammerParser.parse_with pi ii fi parser input cursor status
      ⦃ result => result = .Error .InvalidCursor ⦄ := by
  unfold FoldRepeat.Insts.RusthammerParser.parse_with repeat_run repeat_run_with
  simp only [hmax, core.option.Option.is_none, Option.isNone]
  step with repeat_start_spec input cursor true as ⟨initial, hinitial⟩
  simp [hc] at hinitial
  simp [hinitial, spec_ok]

/-- Specialize the bounded theorem to complete input, then use this to obtain the
public complete-input `parse` contract without any additional callback assumptions. -/
theorem fold_repeat_complete_spec {P I F α R : Type} (pi : Parser P α)
    (ii : core.ops.function.Fn I Unit R) (fi : core.ops.function.Fn F (R × α) R)
    (parser : FoldRepeat P I F) (min max : Nat) (input : Slice U8) (cursor : Cursor)
    (child : Cursor → Spec.ParseResult α → Prop) (initial : R → Prop) (fold : R → α → R → Prop)
    (hp : FoldRepeat.Insts.RusthammerParser.parse_with pi ii fi parser input cursor .Final
      ⦃ result => Spec.boundedFoldRepeat (fun start => Spec.completed (child start))
        initial fold min max cursor result ⦄) :
    Parser.parse.default (FoldRepeat.Insts.RusthammerParser pi ii fi) parser input cursor
      ⦃ result => Spec.boundedFoldRepeatComplete child initial fold min max cursor result ⦄ := by
  apply complete_spec (FoldRepeat.Insts.RusthammerParser pi ii fi) parser input cursor
    (Spec.boundedFoldRepeatComplete child initial fold min max cursor)
  step with hp as ⟨outcome, houtcome⟩
  cases outcome with
  | Success next state => exact ⟨.Ok (next, state), houtcome, rfl⟩
  | Error error => exact ⟨.Err error, houtcome, rfl⟩
  | NeedMore =>
    rcases houtcome with ⟨_, _, _, _, parsed, _, heq⟩
    cases parsed with
    | Err _ => cases heq
    | Ok pair => cases pair; cases heq

theorem fold_repeat_unbounded_complete_spec {P I F α R : Type} (pi : Parser P α)
    (ii : core.ops.function.Fn I Unit R) (fi : core.ops.function.Fn F (R × α) R)
    (parser : FoldRepeat P I F) (min : Nat) (input : Slice U8) (cursor : Cursor)
    (child : Cursor → Spec.ParseResult α → Prop) (initial : R → Prop) (fold : R → α → R → Prop)
    (hp : FoldRepeat.Insts.RusthammerParser.parse_with pi ii fi parser input cursor .Final
      ⦃ result => Spec.unboundedFoldRepeat input (fun start => Spec.completed (child start))
        initial fold min cursor result ⦄) :
    Parser.parse.default (FoldRepeat.Insts.RusthammerParser pi ii fi) parser input cursor
      ⦃ result => Spec.unboundedFoldRepeatComplete input child initial fold min cursor result ⦄ := by
  apply complete_spec (FoldRepeat.Insts.RusthammerParser pi ii fi) parser input cursor
    (Spec.unboundedFoldRepeatComplete input child initial fold min cursor)
  step with hp as ⟨outcome, houtcome⟩
  cases outcome with
  | Success next state => exact ⟨.Ok (next, state), houtcome, rfl⟩
  | Error error => exact ⟨.Err error, houtcome, rfl⟩
  | NeedMore =>
    by_cases hv : Spec.validCursor input cursor
    · simp only [Spec.unboundedFoldRepeat, Spec.accumulated, Spec.unboundedRepetition, if_pos hv] at houtcome
      rcases houtcome with ⟨_, _, _, _, parsed, _, heq⟩
      cases parsed with
      | Err _ => cases heq
      | Ok pair => cases pair; cases heq
    · simp [Spec.unboundedFoldRepeat, Spec.accumulated, Spec.unboundedRepetition, hv] at houtcome

end RustHammer.Proofs
