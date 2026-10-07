import RustHammer.SepByProofs

open RustHammer.Code.grammar.repeat
  RustHammer.Code.grammar.sequence
  RustHammer.Code.input_types

open Aeneas Aeneas.Std Result WP

namespace RustHammer.Proofs
open Code

/-- A zero cap needs only initialization: neither the first parser nor a following
parser is invoked. This also applies to invalid raw cursors and partial input. -/
theorem repeat_run_with_zero {P Q A α R : Type} (pi : DirectParser P α) (qi : DirectParser Q α)
    (ai : RepeatAccumulator A α R) (parser : P) (following : Q) (accumulator : A)
    (input : Slice U8) (cursor : Cursor) (context : ParseContext)
    (initial : R → Prop) (hi : ai.init accumulator ⦃ result => initial result ⦄) :
    DirectRun.repeat_run_with pi qi ai parser following { min := 0#usize, max := some 0#usize }
      accumulator input cursor context ⦃ result => ∃ state, initial state ∧ result = .Success cursor state ⦄ := by
  rw [DirectRun.repeat_run_with_eq]
  simp only [core.option.Option.is_none, Option.isNone, repeat_start, Bool.false_eq_true, ↓reduceIte, bind_ok]
  step with hi as ⟨state, hstate⟩
  unfold DirectRun.repeat_run_with_loop
  apply direct_projection_spec
  unfold repeat_run_with_loop loop
  simp [repeat_run_with_loop.body, repeat_below_max, spec_ok, hstate]

theorem sep_by_zero {P S α β : Type} (pi : DirectParser P α) (si : DirectParser S β) (parser : P) (separator : S)
    (input : Slice U8) (cursor : Cursor) (context : ParseContext) :
    SepBy.Insts.RusthammerParserInputVec.parse_with pi si
      { parser, separator, bounds := { min := 0#usize, max := some 0#usize } } input cursor context
      ⦃ result => result = .Success cursor (alloc.vec.Vec.new α) ⦄ := by
  rw [SepBy.Insts.RusthammerParserInputVec.parse_with_eq]
  have h := repeat_run_with_zero pi
    (Right.Insts.RusthammerParser (Shared0P.Insts.RusthammerParser si) (Shared0P.Insts.RusthammerParser pi)) (Collect.Insts.RusthammerGrammarRepeatRepeatAccumulatorAVec α)
    parser { first := separator, second := parser } () input cursor context
    (fun state => state = alloc.vec.Vec.new α)
    (by simp [Collect.Insts.RusthammerGrammarRepeatRepeatAccumulatorAVec.init, spec_ok])
  simpa using h

theorem fold_sep_by_zero {P S I F α β R : Type} (pi : DirectParser P α) (si : DirectParser S β)
    (ii : core.ops.function.Fn I Unit R) (fi : core.ops.function.Fn F (R × α) R)
    (parser : P) (separator : S) (init : I) (fold : F)
    (input : Slice U8) (cursor : Cursor) (context : ParseContext)
    (initial : R → Prop) (hi : ii.call init () ⦃ result => initial result ⦄) :
    FoldSepBy.Insts.RusthammerParser.parse_with pi si ii fi
      { parser, separator, bounds := { min := 0#usize, max := some 0#usize }, init, fold } input cursor context
      ⦃ result => ∃ state, initial state ∧ result = .Success cursor state ⦄ := by
  rw [FoldSepBy.Insts.RusthammerParser.parse_with_eq]
  apply repeat_run_with_zero pi
    (Right.Insts.RusthammerParser (Shared0P.Insts.RusthammerParser si) (Shared0P.Insts.RusthammerParser pi)) (FoldSepBy.Insts.RusthammerGrammarRepeatRepeatAccumulator P S ii fi)
    parser { first := separator, second := parser }
    { parser, separator, bounds := { min := 0#usize, max := some 0#usize }, init, fold }
    input cursor context initial hi

/-- An invalid unbounded starting cursor requires no child or accumulator contracts. -/
theorem repeat_run_with_invalid_cursor {P Q A α R : Type} (pi : DirectParser P α) (qi : DirectParser Q α)
    (ai : RepeatAccumulator A α R) (parser : P) (following : Q) (bounds : RepeatBounds) (accumulator : A)
    (input : Slice U8) (cursor : Cursor) (context : ParseContext)
    (hmax : bounds.max = none) (hc : ¬Spec.validCursor input cursor) :
    DirectRun.repeat_run_with pi qi ai parser following bounds accumulator input cursor context
      ⦃ result => result = .Error .InvalidCursor ⦄ := by
  rw [DirectRun.repeat_run_with_eq]
  simp only [hmax, core.option.Option.is_none, Option.isNone]
  step with repeat_start_spec input cursor true as ⟨initial, hinitial⟩
  simp [hc] at hinitial
  simp [hinitial, spec_ok]

theorem sep_by_unbounded_invalid_cursor {P S α β : Type} (pi : DirectParser P α) (si : DirectParser S β)
    (parser : SepBy P S) (hmax : parser.bounds.max = none)
    (input : Slice U8) (cursor : Cursor) (context : ParseContext) (hc : ¬Spec.validCursor input cursor) :
    SepBy.Insts.RusthammerParserInputVec.parse_with pi si parser input cursor context
      ⦃ result => result = .Error .InvalidCursor ⦄ := by
  apply repeat_run_with_invalid_cursor pi
    (Right.Insts.RusthammerParser (Shared0P.Insts.RusthammerParser si) (Shared0P.Insts.RusthammerParser pi)) _ parser.parser _ parser.bounds () input cursor context hmax hc

theorem fold_sep_by_unbounded_invalid_cursor {P S I F α β R : Type} (pi : DirectParser P α) (si : DirectParser S β)
    (ii : core.ops.function.Fn I Unit R) (fi : core.ops.function.Fn F (R × α) R)
    (parser : FoldSepBy P S I F) (hmax : parser.bounds.max = none)
    (input : Slice U8) (cursor : Cursor) (context : ParseContext) (hc : ¬Spec.validCursor input cursor) :
    FoldSepBy.Insts.RusthammerParser.parse_with pi si ii fi parser input cursor context
      ⦃ result => result = .Error .InvalidCursor ⦄ := by
  apply repeat_run_with_invalid_cursor pi
    (Right.Insts.RusthammerParser (Shared0P.Insts.RusthammerParser si) (Shared0P.Insts.RusthammerParser pi)) _ parser.parser _ parser.bounds parser input cursor context hmax hc

/-- Both collection and folding count only item values, including unit outputs. -/
theorem sep_by_exact_length {α β : Type} (item : Cursor → ParseOutcome α → Prop)
    (sep : Cursor → ParseOutcome β → Prop) (count : Nat) (cursor next : Cursor) (values : alloc.vec.Vec α)
    (h : Spec.boundedSepBy item sep count count cursor (.Success next values)) : values.val.length = count := by
  have hlo := h.1
  have hhi := h.2.1
  omega

theorem fold_sep_by_exact_items {α β R : Type} (item : Cursor → ParseOutcome α → Prop)
    (sep : Cursor → ParseOutcome β → Prop) (initial : R → Prop) (fold : R → α → R → Prop)
    (count : Nat) (cursor next : Cursor) (state : R)
    (h : Spec.boundedFoldSepBy item sep initial fold count count cursor (.Success next state)) :
    ∃ values, values.length = count ∧ Spec.indexedRepetitions (Spec.separatedAttempt item sep) cursor values next ∧
      Spec.folds initial fold values state := by
  rcases h with ⟨values, hfold, hlo, hhi, hprefix, _⟩
  exact ⟨values, by omega, hprefix, hfold⟩

theorem indexed_advancing_consumption {α : Type} (input : Slice U8)
    (child : Nat → Cursor → ParseOutcome α → Prop) (cursor next : Cursor) (values : List α)
    (h : Spec.indexedRepetitions (fun n => Spec.advancing input (child n)) cursor values next) :
    Spec.position cursor + values.length ≤ Spec.position next := by
  induction h with
  | empty => simp
  | append _ last ih =>
    have hstep := last.2.2
    simp only [List.length_append, List.length_singleton]
    omega

end RustHammer.Proofs
