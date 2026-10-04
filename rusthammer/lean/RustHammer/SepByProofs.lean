import RustHammer.SepBySupport

open Aeneas Aeneas.Std Result WP

namespace RustHammer.Proofs
open Code

theorem sep_by_new_spec {P S : Type} (parser : P) (separator : S) (min max : Usize) :
    SepBy.new parser separator min max
      ⦃ result => Spec.sepByNewOutcome parser separator min max result ⦄ := by
  by_cases hbounds : min.val ≤ max.val
  · have h : ¬min > max := by scalar_tac
    simp [SepBy.new, RepeatBounds.new, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      Spec.sepByNewOutcome, hbounds, h, spec_ok]
  · have h : min > max := by scalar_tac
    simp [SepBy.new, RepeatBounds.new, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      Spec.sepByNewOutcome, hbounds, h, spec_ok]

theorem sep_by_new_valid {P S : Type} (child : P) (separator : S) (min max : Usize)
    (parser : SepBy P S) (hnew : SepBy.new child separator min max = ok (.Ok parser)) :
    Spec.validSepBy parser := by
  have hspec := sep_by_new_spec child separator min max
  rw [hnew] at hspec
  simp only [spec_ok, Spec.sepByNewOutcome] at hspec
  split at hspec
  · cases hspec
    simpa [Spec.validSepBy, Spec.validRepeatBounds] using (show min.val ≤ max.val from ‹_›)
  · cases hspec

theorem sep_by_exact_spec {P S : Type} (parser : P) (separator : S) (count : Usize) :
    SepBy.exact parser separator count ⦃ result =>
      result = { parser, separator, bounds := { min := count, max := some count } } ∧
      Spec.validSepBy result ⦄ := by
  simp [SepBy.exact, RepeatBounds.exact, Spec.validSepBy, Spec.validRepeatBounds, spec_ok]

theorem sep_by_at_least_spec {P S : Type} (parser : P) (separator : S) (min : Usize) :
    SepBy.at_least parser separator min ⦃ result =>
      result = { parser, separator, bounds := { min, max := none } } ∧ Spec.validSepBy result ⦄ := by
  simp [SepBy.at_least, RepeatBounds.at_least, Spec.validSepBy, Spec.validRepeatBounds, spec_ok]

theorem sep_by_min_spec {P S : Type} (parser : SepBy P S) :
    SepBy.min parser ⦃ result => result = parser.bounds.min ⦄ := by
  simp [SepBy.min, spec_ok]

theorem sep_by_max_spec {P S : Type} (parser : SepBy P S) :
    SepBy.max parser ⦃ result => result = parser.bounds.max ⦄ := by
  simp [SepBy.max, spec_ok]

theorem fold_sep_by_new_spec {P S I F : Type} (parser : P) (separator : S) (min max : Usize) (init : I) (fold : F) :
    FoldSepBy.new parser separator min max init fold
      ⦃ result => Spec.foldSepByNewOutcome parser separator min max init fold result ⦄ := by
  by_cases hbounds : min.val ≤ max.val
  · have h : ¬min > max := by scalar_tac
    simp [FoldSepBy.new, RepeatBounds.new, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      Spec.foldSepByNewOutcome, hbounds, h, spec_ok]
  · have h : min > max := by scalar_tac
    simp [FoldSepBy.new, RepeatBounds.new, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      Spec.foldSepByNewOutcome, hbounds, h, spec_ok]

theorem fold_sep_by_new_valid {P S I F : Type} (child : P) (separator : S) (min max : Usize) (init : I) (fold : F)
    (parser : FoldSepBy P S I F) (hnew : FoldSepBy.new child separator min max init fold = ok (.Ok parser)) :
    Spec.validFoldSepBy parser := by
  have hspec := fold_sep_by_new_spec child separator min max init fold
  rw [hnew] at hspec
  simp only [spec_ok, Spec.foldSepByNewOutcome] at hspec
  split at hspec
  · cases hspec
    simpa [Spec.validFoldSepBy, Spec.validRepeatBounds] using (show min.val ≤ max.val from ‹_›)
  · cases hspec

theorem fold_sep_by_exact_spec {P S I F : Type} (parser : P) (separator : S) (count : Usize) (init : I) (fold : F) :
    FoldSepBy.exact parser separator count init fold ⦃ result =>
      result = { parser, separator, bounds := { min := count, max := some count }, init, fold } ∧
      Spec.validFoldSepBy result ⦄ := by
  simp [FoldSepBy.exact, RepeatBounds.exact, Spec.validFoldSepBy, Spec.validRepeatBounds, spec_ok]

theorem fold_sep_by_at_least_spec {P S I F : Type} (parser : P) (separator : S) (min : Usize) (init : I) (fold : F) :
    FoldSepBy.at_least parser separator min init fold ⦃ result =>
      result = { parser, separator, bounds := { min, max := none }, init, fold } ∧ Spec.validFoldSepBy result ⦄ := by
  simp [FoldSepBy.at_least, RepeatBounds.at_least, Spec.validFoldSepBy, Spec.validRepeatBounds, spec_ok]

theorem fold_sep_by_min_spec {P S I F : Type} (parser : FoldSepBy P S I F) :
    FoldSepBy.min parser ⦃ result => result = parser.bounds.min ⦄ := by
  simp [FoldSepBy.min, spec_ok]

theorem fold_sep_by_max_spec {P S I F : Type} (parser : FoldSepBy P S I F) :
    FoldSepBy.max parser ⦃ result => result = parser.bounds.max ⦄ := by
  simp [FoldSepBy.max, spec_ok]

/-- Bounded lists retain only items and roll back whole rejected separator/item
attempts. Finite empty successes are allowed; the item count bounds execution. -/
theorem sep_by_with_spec {P S α β : Type} (pi : Parser P α) (si : Parser S β)
    (parser : SepBy P S) (max : Usize) (hmax : parser.bounds.max = some max)
    (input : Slice U8) (cursor : Cursor) (status : InputStatus) (hconfig : Spec.validSepBy parser)
    (item : Cursor → ParseOutcome α → Prop) (sep : Cursor → ParseOutcome β → Prop)
    (hp : ∀ start, pi.parse_with parser.parser input start status ⦃ result => item start result ⦄)
    (hs : ∀ start, si.parse_with parser.separator input start status ⦃ result => sep start result ⦄) :
    SepBy.Insts.RusthammerParserInputVec.parse_with pi si parser input cursor status
      ⦃ result => Spec.boundedSepBy item sep parser.bounds.min.val max.val cursor result ⦄ := by
  have hb : parser.bounds = { min := parser.bounds.min, max := some max } := by
    cases h : parser.bounds; simp_all
  unfold SepBy.Insts.RusthammerParserInputVec.parse_with
  rw [hb]
  step with repeat_run_with_bounded_spec pi
    (Right.Insts.RusthammerParser (Shared0P.Insts.RusthammerParser si) (Shared0P.Insts.RusthammerParser pi)) (Collect.Insts.RusthammerRepeatAccumulatorAVec α)
    parser.parser { first := parser.separator, second := parser.parser }
    parser.bounds.min max () input cursor status (hconfig max hmax) (Spec.separatedAttempt item sep)
    (fun values state => state.val = values)
    (fun count start => separated_attempt_spec pi si parser.parser parser.separator count input start status item sep hp hs)
    (by simp [Collect.Insts.RusthammerRepeatAccumulatorAVec.init, spec_ok])
    (by
      intro values next after value state _ _ hlen hstate
      simp only [Collect.Insts.RusthammerRepeatAccumulatorAVec.step]
      step with alloc.vec.Vec.push_spec state value (by clear hb; scalar_tac) as ⟨appended, happended⟩
      simpa [hstate] using happended) as ⟨outcome, houtcome⟩
  exact (accumulated_collection _ outcome).mp houtcome

/-- Progress is checked for the first item and then each complete pair, without
requiring the separator and following item to advance separately. -/
theorem sep_by_unbounded_with_spec {P S α β : Type} (pi : Parser P α) (si : Parser S β)
    (parser : SepBy P S) (hmax : parser.bounds.max = none)
    (input : Slice U8) (cursor : Cursor) (status : InputStatus)
    (item : Cursor → ParseOutcome α → Prop) (sep : Cursor → ParseOutcome β → Prop)
    (hp : ∀ start, pi.parse_with parser.parser input start status ⦃ result => item start result ⦄)
    (hs : ∀ start, si.parse_with parser.separator input start status ⦃ result => sep start result ⦄) :
    SepBy.Insts.RusthammerParserInputVec.parse_with pi si parser input cursor status
      ⦃ result => Spec.unboundedSepBy input item sep parser.bounds.min.val cursor result ⦄ := by
  have hb : parser.bounds = { min := parser.bounds.min, max := none } := by
    cases h : parser.bounds; simp_all
  unfold SepBy.Insts.RusthammerParserInputVec.parse_with
  rw [hb]
  step with repeat_run_with_unbounded_spec pi
    (Right.Insts.RusthammerParser (Shared0P.Insts.RusthammerParser si) (Shared0P.Insts.RusthammerParser pi)) (Collect.Insts.RusthammerRepeatAccumulatorAVec α)
    parser.parser { first := parser.separator, second := parser.parser }
    parser.bounds.min () input cursor status (Spec.separatedAttempt item sep)
    (fun values state => state.val = values)
    (fun count start => separated_attempt_spec pi si parser.parser parser.separator count input start status item sep hp hs)
    (by simp [Collect.Insts.RusthammerRepeatAccumulatorAVec.init, spec_ok])
    (by
      intro values next after value state _ _ hlen hstate
      simp only [Collect.Insts.RusthammerRepeatAccumulatorAVec.step]
      step with alloc.vec.Vec.push_spec state value (by simpa only [hstate] using hlen) as ⟨appended, happended⟩
      simpa [hstate] using happended) as ⟨outcome, houtcome⟩
  exact (accumulated_collection _ outcome).mp houtcome

/-- Folding uses precisely the same item sequence and stopping specification as
collection; neither rejected attempts nor separator values enter the fold. -/
theorem fold_sep_by_with_spec {P S I F α β R : Type} (pi : Parser P α) (si : Parser S β)
    (ii : core.ops.function.Fn I Unit R) (fi : core.ops.function.Fn F (R × α) R)
    (parser : FoldSepBy P S I F) (max : Usize) (hmax : parser.bounds.max = some max)
    (input : Slice U8) (cursor : Cursor) (status : InputStatus) (hconfig : Spec.validFoldSepBy parser)
    (item : Cursor → ParseOutcome α → Prop) (sep : Cursor → ParseOutcome β → Prop)
    (initial : R → Prop) (fold : R → α → R → Prop)
    (hp : ∀ start, pi.parse_with parser.parser input start status ⦃ result => item start result ⦄)
    (hs : ∀ start, si.parse_with parser.separator input start status ⦃ result => sep start result ⦄)
    (hi : ii.call parser.init () ⦃ result => initial result ⦄)
    (hf : ∀ values next after value state,
      Spec.indexedRepetitions (Spec.separatedAttempt item sep) cursor values next →
      Spec.separatedAttempt item sep values.length next (.Success after value) →
      values.length < max.val → Spec.folds initial fold values state →
      fi.call parser.fold (state, value) ⦃ result => fold state value result ⦄) :
    FoldSepBy.Insts.RusthammerParser.parse_with pi si ii fi parser input cursor status
      ⦃ result => Spec.boundedFoldSepBy item sep initial fold parser.bounds.min.val max.val cursor result ⦄ := by
  have hb : parser.bounds = { min := parser.bounds.min, max := some max } := by
    cases h : parser.bounds; simp_all
  unfold FoldSepBy.Insts.RusthammerParser.parse_with
  rw [hb]
  apply repeat_run_with_bounded_spec pi
    (Right.Insts.RusthammerParser (Shared0P.Insts.RusthammerParser si) (Shared0P.Insts.RusthammerParser pi)) (FoldSepBy.Insts.RusthammerRepeatAccumulator P S ii fi)
    parser.parser { first := parser.separator, second := parser.parser }
    parser.bounds.min max parser input cursor status (hconfig max hmax)
    (Spec.separatedAttempt item sep) (Spec.folds initial fold)
    (fun count start => separated_attempt_spec pi si parser.parser parser.separator count input start status item sep hp hs)
  · simp only [FoldSepBy.Insts.RusthammerRepeatAccumulator.init]
    step with hi as ⟨state, hstate⟩
    exact Spec.folds.empty hstate
  · intro values next after value state hprefix hchild hlen hstate
    simp only [FoldSepBy.Insts.RusthammerRepeatAccumulator.step]
    step with hf values next after value state hprefix hchild hlen hstate as ⟨following, hfollowing⟩
    exact Spec.folds.append hstate hfollowing

theorem fold_sep_by_unbounded_with_spec {P S I F α β R : Type} (pi : Parser P α) (si : Parser S β)
    (ii : core.ops.function.Fn I Unit R) (fi : core.ops.function.Fn F (R × α) R)
    (parser : FoldSepBy P S I F) (hmax : parser.bounds.max = none)
    (input : Slice U8) (cursor : Cursor) (status : InputStatus)
    (item : Cursor → ParseOutcome α → Prop) (sep : Cursor → ParseOutcome β → Prop)
    (initial : R → Prop) (fold : R → α → R → Prop)
    (hp : ∀ start, pi.parse_with parser.parser input start status ⦃ result => item start result ⦄)
    (hs : ∀ start, si.parse_with parser.separator input start status ⦃ result => sep start result ⦄)
    (hi : ii.call parser.init () ⦃ result => initial result ⦄)
    (hf : ∀ values next after value state,
      Spec.indexedRepetitions (fun n => Spec.advancing input (Spec.separatedAttempt item sep n)) cursor values next →
      Spec.advancing input (Spec.separatedAttempt item sep values.length) next (.Success after value) →
      values.length < Usize.max → Spec.folds initial fold values state →
      fi.call parser.fold (state, value) ⦃ result => fold state value result ⦄) :
    FoldSepBy.Insts.RusthammerParser.parse_with pi si ii fi parser input cursor status
      ⦃ result => Spec.unboundedFoldSepBy input item sep initial fold parser.bounds.min.val cursor result ⦄ := by
  have hb : parser.bounds = { min := parser.bounds.min, max := none } := by
    cases h : parser.bounds; simp_all
  unfold FoldSepBy.Insts.RusthammerParser.parse_with
  rw [hb]
  apply repeat_run_with_unbounded_spec pi
    (Right.Insts.RusthammerParser (Shared0P.Insts.RusthammerParser si) (Shared0P.Insts.RusthammerParser pi)) (FoldSepBy.Insts.RusthammerRepeatAccumulator P S ii fi)
    parser.parser { first := parser.separator, second := parser.parser }
    parser.bounds.min parser input cursor status (Spec.separatedAttempt item sep) (Spec.folds initial fold)
    (fun count start => separated_attempt_spec pi si parser.parser parser.separator count input start status item sep hp hs)
  · simp only [FoldSepBy.Insts.RusthammerRepeatAccumulator.init]
    step with hi as ⟨state, hstate⟩
    exact Spec.folds.empty hstate
  · intro values next after value state hprefix hchild hlen hstate
    simp only [FoldSepBy.Insts.RusthammerRepeatAccumulator.step]
    step with hf values next after value state hprefix hchild hlen hstate as ⟨following, hfollowing⟩
    exact Spec.folds.append hstate hfollowing

theorem sep_by_final_spec {P S α β : Type} (pi : Parser P α) (si : Parser S β)
    (parser : SepBy P S) (max : Usize) (hmax : parser.bounds.max = some max)
    (input : Slice U8) (cursor : Cursor) (hconfig : Spec.validSepBy parser)
    (item : Cursor → Spec.ParseResult α → Prop) (sep : Cursor → Spec.ParseResult β → Prop)
    (hp : ∀ start, pi.parse_with parser.parser input start .Final ⦃ result => Spec.completed (item start) result ⦄)
    (hs : ∀ start, si.parse_with parser.separator input start .Final ⦃ result => Spec.completed (sep start) result ⦄) :
    SepBy.Insts.RusthammerParserInputVec.parse_with pi si parser input cursor .Final
      ⦃ result => Spec.completed (Spec.boundedSepByComplete item sep parser.bounds.min.val max.val cursor) result ⦄ := by
  step with sep_by_with_spec pi si parser max hmax input cursor .Final hconfig
    (fun start => Spec.completed (item start)) (fun start => Spec.completed (sep start)) hp hs as ⟨outcome, houtcome⟩
  cases outcome with
  | Success next values => exact ⟨.Ok (next, values), houtcome, rfl⟩
  | Error error => exact ⟨.Err error, houtcome, rfl⟩
  | NeedMore =>
    rcases houtcome with ⟨values, next, _, _, hincomplete⟩
    exact (separated_attempt_complete_not_need_more item sep values.length next hincomplete).elim

theorem sep_by_spec {P S α β : Type} (pi : Parser P α) (si : Parser S β)
    (parser : SepBy P S) (max : Usize) (hmax : parser.bounds.max = some max)
    (input : Slice U8) (cursor : Cursor) (hconfig : Spec.validSepBy parser)
    (item : Cursor → Spec.ParseResult α → Prop) (sep : Cursor → Spec.ParseResult β → Prop)
    (hp : ∀ start, pi.parse_with parser.parser input start .Final ⦃ result => Spec.completed (item start) result ⦄)
    (hs : ∀ start, si.parse_with parser.separator input start .Final ⦃ result => Spec.completed (sep start) result ⦄) :
    Parser.parse.default (SepBy.Insts.RusthammerParserInputVec pi si) parser input cursor
      ⦃ result => Spec.boundedSepByComplete item sep parser.bounds.min.val max.val cursor result ⦄ := by
  exact complete_spec (SepBy.Insts.RusthammerParserInputVec pi si) parser input cursor
    (Spec.boundedSepByComplete item sep parser.bounds.min.val max.val cursor)
    (sep_by_final_spec pi si parser max hmax input cursor hconfig item sep hp hs)

theorem sep_by_unbounded_final_spec {P S α β : Type} (pi : Parser P α) (si : Parser S β)
    (parser : SepBy P S) (hmax : parser.bounds.max = none)
    (input : Slice U8) (cursor : Cursor)
    (item : Cursor → Spec.ParseResult α → Prop) (sep : Cursor → Spec.ParseResult β → Prop)
    (hp : ∀ start, pi.parse_with parser.parser input start .Final ⦃ result => Spec.completed (item start) result ⦄)
    (hs : ∀ start, si.parse_with parser.separator input start .Final ⦃ result => Spec.completed (sep start) result ⦄) :
    SepBy.Insts.RusthammerParserInputVec.parse_with pi si parser input cursor .Final
      ⦃ result => Spec.completed (Spec.unboundedSepByComplete input item sep parser.bounds.min.val cursor) result ⦄ := by
  step with sep_by_unbounded_with_spec pi si parser hmax input cursor .Final
    (fun start => Spec.completed (item start)) (fun start => Spec.completed (sep start)) hp hs as ⟨outcome, houtcome⟩
  cases outcome with
  | Success next values => exact ⟨.Ok (next, values), houtcome, rfl⟩
  | Error error => exact ⟨.Err error, houtcome, rfl⟩
  | NeedMore =>
    by_cases hv : Spec.validCursor input cursor
    · simp only [Spec.unboundedSepBy, Spec.collectedValues, Spec.unboundedIterations, if_pos hv] at houtcome
      rcases houtcome with ⟨values, next, _, _, hincomplete⟩
      exact (separated_attempt_complete_not_need_more item sep values.length next hincomplete).elim
    · simp [Spec.unboundedSepBy, Spec.collectedValues, Spec.unboundedIterations, hv] at houtcome

theorem sep_by_unbounded_spec {P S α β : Type} (pi : Parser P α) (si : Parser S β)
    (parser : SepBy P S) (hmax : parser.bounds.max = none)
    (input : Slice U8) (cursor : Cursor)
    (item : Cursor → Spec.ParseResult α → Prop) (sep : Cursor → Spec.ParseResult β → Prop)
    (hp : ∀ start, pi.parse_with parser.parser input start .Final ⦃ result => Spec.completed (item start) result ⦄)
    (hs : ∀ start, si.parse_with parser.separator input start .Final ⦃ result => Spec.completed (sep start) result ⦄) :
    Parser.parse.default (SepBy.Insts.RusthammerParserInputVec pi si) parser input cursor
      ⦃ result => Spec.unboundedSepByComplete input item sep parser.bounds.min.val cursor result ⦄ := by
  exact complete_spec (SepBy.Insts.RusthammerParserInputVec pi si) parser input cursor
    (Spec.unboundedSepByComplete input item sep parser.bounds.min.val cursor)
    (sep_by_unbounded_final_spec pi si parser hmax input cursor item sep hp hs)

theorem fold_sep_by_complete_spec {P S I F α β R : Type} (pi : Parser P α) (si : Parser S β)
    (ii : core.ops.function.Fn I Unit R) (fi : core.ops.function.Fn F (R × α) R)
    (parser : FoldSepBy P S I F) (min max : Nat) (input : Slice U8) (cursor : Cursor)
    (item : Cursor → Spec.ParseResult α → Prop) (sep : Cursor → Spec.ParseResult β → Prop)
    (initial : R → Prop) (fold : R → α → R → Prop)
    (hp : FoldSepBy.Insts.RusthammerParser.parse_with pi si ii fi parser input cursor .Final
      ⦃ result => Spec.boundedFoldSepBy (fun start => Spec.completed (item start))
        (fun start => Spec.completed (sep start)) initial fold min max cursor result ⦄) :
    Parser.parse.default (FoldSepBy.Insts.RusthammerParser pi si ii fi) parser input cursor
      ⦃ result => Spec.boundedFoldSepByComplete item sep initial fold min max cursor result ⦄ := by
  apply complete_spec (FoldSepBy.Insts.RusthammerParser pi si ii fi) parser input cursor
    (Spec.boundedFoldSepByComplete item sep initial fold min max cursor)
  step with hp as ⟨outcome, houtcome⟩
  cases outcome with
  | Success next state => exact ⟨.Ok (next, state), houtcome, rfl⟩
  | Error error => exact ⟨.Err error, houtcome, rfl⟩
  | NeedMore =>
    rcases houtcome with ⟨values, next, _, _, hincomplete⟩
    exact (separated_attempt_complete_not_need_more item sep values.length next hincomplete).elim

theorem fold_sep_by_unbounded_complete_spec {P S I F α β R : Type} (pi : Parser P α) (si : Parser S β)
    (ii : core.ops.function.Fn I Unit R) (fi : core.ops.function.Fn F (R × α) R)
    (parser : FoldSepBy P S I F) (min : Nat) (input : Slice U8) (cursor : Cursor)
    (item : Cursor → Spec.ParseResult α → Prop) (sep : Cursor → Spec.ParseResult β → Prop)
    (initial : R → Prop) (fold : R → α → R → Prop)
    (hp : FoldSepBy.Insts.RusthammerParser.parse_with pi si ii fi parser input cursor .Final
      ⦃ result => Spec.unboundedFoldSepBy input (fun start => Spec.completed (item start))
        (fun start => Spec.completed (sep start)) initial fold min cursor result ⦄) :
    Parser.parse.default (FoldSepBy.Insts.RusthammerParser pi si ii fi) parser input cursor
      ⦃ result => Spec.unboundedFoldSepByComplete input item sep initial fold min cursor result ⦄ := by
  apply complete_spec (FoldSepBy.Insts.RusthammerParser pi si ii fi) parser input cursor
    (Spec.unboundedFoldSepByComplete input item sep initial fold min cursor)
  step with hp as ⟨outcome, houtcome⟩
  cases outcome with
  | Success next state => exact ⟨.Ok (next, state), houtcome, rfl⟩
  | Error error => exact ⟨.Err error, houtcome, rfl⟩
  | NeedMore =>
    by_cases hv : Spec.validCursor input cursor
    · simp only [Spec.unboundedFoldSepBy, Spec.accumulated, Spec.unboundedIterations, if_pos hv] at houtcome
      rcases houtcome with ⟨values, next, _, _, hincomplete⟩
      exact (separated_attempt_complete_not_need_more item sep values.length next hincomplete).elim
    · simp [Spec.unboundedFoldSepBy, Spec.accumulated, Spec.unboundedIterations, hv] at houtcome

end RustHammer.Proofs
