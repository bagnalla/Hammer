import RustHammer.IntRangeSpec
import RustHammer.SelectionProofs
import RustHammer.IntegerProofs

open RustHammer.Code.grammar.numeric
  RustHammer.Code.grammar.transform
  RustHammer.Code.input_types
  RustHammer.Code.parser_traits

open Aeneas Aeneas.Std Result WP

namespace RustHammer.Proofs
open Code

/-- Comparisons in user-defined Ord implementations require contracts, just like
Verify callbacks. Native scalar comparisons satisfy these hypotheses directly. -/
theorem int_range_new_spec {P T : Type} (pi : parser_traits.Parser P T) (oi : core.cmp.Ord T)
    (child : P) (lower upper : T) (le : T → T → Prop) [DecidableRel le]
    (hgt : oi.partialOrdInst.gt lower upper ⦃ result => result = decide (¬ le lower upper) ⦄) :
    IntRange.new pi oi child lower upper
      ⦃ result => Spec.intRangeNewOutcome le child lower upper result ⦄ := by
  unfold IntRange.new
  step with hgt as ⟨reversed, hreversed⟩
  by_cases h : le lower upper <;> simp [hreversed, h, Spec.intRangeNewOutcome, spec_ok]

theorem int_range_new_valid {P T : Type} (pi : parser_traits.Parser P T) (oi : core.cmp.Ord T)
    (child : P) (lower upper : T) (parser : IntRange P T)
    (le : T → T → Prop) [DecidableRel le]
    (hgt : oi.partialOrdInst.gt lower upper ⦃ result => result = decide (¬ le lower upper) ⦄)
    (hnew : IntRange.new pi oi child lower upper = ok (.Ok parser)) :
    Spec.validIntRange le parser := by
  have h := int_range_new_spec pi oi child lower upper le hgt
  rw [hnew] at h
  simp only [spec_ok, Spec.intRangeNewOutcome] at h
  split at h
  · cases h
    assumption
  · cases h

theorem int_range_lower_spec {P T : Type} (parser : IntRange P T) :
    IntRange.impl.lower parser ⦃ result => result = parser.lower ⦄ := by
  simp [IntRange.impl.lower, spec_ok]

theorem int_range_upper_spec {P T : Type} (parser : IntRange P T) :
    IntRange.impl.upper parser ⦃ result => result = parser.upper ⦄ := by
  simp [IntRange.impl.upper, spec_ok]

theorem int_range_clone_spec {P T : Type} (pc : core.clone.Clone P) (tc : core.clone.Clone T)
    (parser : IntRange P T)
    (hp : pc.clone parser.parser ⦃ result => result = parser.parser ⦄)
    (hl : tc.clone parser.lower ⦃ result => result = parser.lower ⦄)
    (hu : tc.clone parser.upper ⦃ result => result = parser.upper ⦄) :
    IntRange.Insts.CoreCloneClone.clone pc tc parser ⦃ result => result = parser ⦄ := by
  unfold IntRange.Insts.CoreCloneClone.clone
  step with hp as ⟨child, hchild⟩
  step with hl as ⟨lower, hlower⟩
  step with hu as ⟨upper, hupper⟩
  simp [hchild, hlower, hupper]

theorem int_range_predicate_spec {P T : Type} (pi : parser_traits.Parser P T) (oi : core.cmp.Ord T)
    (parser : IntRange P T) (value : T) (le : T → T → Prop) [DecidableRel le]
    (hle : ∀ a b, oi.partialOrdInst.le a b ⦃ result => result = decide (le a b) ⦄) :
    ParserInputIntRangeT.parse_with.closure.Insts.CoreOpsFunctionFnTupleShared1TBool.call
      pi oi parser value ⦃ result => result = decide (Spec.inRange le parser.lower parser.upper value) ⦄ := by
  unfold ParserInputIntRangeT.parse_with.closure.Insts.CoreOpsFunctionFnTupleShared1TBool.call
  step with hle parser.lower value as ⟨above, habove⟩
  by_cases h : le parser.lower value
  · simp only [habove, h, decide_true, ↓reduceIte]
    step with hle value parser.upper as ⟨below, hbelow⟩
    simp [Spec.inRange, h, hbelow]
  · simp [habove, h, Spec.inRange, spec_ok]

/-- Range validation is exactly Verify with a proved inclusive predicate.
No extra cursor checks or bound revalidation are inserted at parse time. -/
theorem int_range_with_spec {P T : Type} (pi : parser_traits.Parser P T) (oi : core.cmp.Ord T)
    (parser : IntRange P T) (input : Slice U8) (cursor : Cursor) (context : ByteOrder)
    (child : Cursor → Spec.ParseResult T → Prop) (le : T → T → Prop) [DecidableRel le]
    (hp : pi.parse_with parser.parser input cursor context ⦃ result => child cursor result ⦄)
    (hle : ∀ a b, oi.partialOrdInst.le a b ⦃ result => result = decide (le a b) ⦄) :
    IntRange.Insts.RusthammerParser_traitsParser.parse_with pi oi parser input cursor context
      ⦃ result => Contracts.verify child (Spec.inRange le parser.lower parser.upper) cursor result ⦄ := by
  rw [IntRange.Insts.RusthammerParser_traitsParser.parse_with]
  apply verify_with_spec (Shared0P.Insts.RusthammerParser_traitsParser pi)
    (ParserInputIntRangeT.parse_with.closure.Insts.CoreOpsFunctionFnTupleShared1TBool pi oi)
    { parser := parser.parser, predicate := parser } input cursor context child
    (Spec.inRange le parser.lower parser.upper) hp
  intro next value _hvalue
  exact int_range_predicate_spec pi oi parser value le hle

theorem int_range_final_spec {P T : Type} (pi : parser_traits.Parser P T) (oi : core.cmp.Ord T)
    (parser : IntRange P T) (input : Slice U8) (cursor : Cursor)
    (child : Cursor → Spec.ParseResult T → Prop) (le : T → T → Prop) [DecidableRel le]
    (hp : pi.parse_with parser.parser input cursor ByteOrder.Big ⦃ result => Spec.satisfies (child cursor) result ⦄)
    (hle : ∀ a b, oi.partialOrdInst.le a b ⦃ result => result = decide (le a b) ⦄) :
    IntRange.Insts.RusthammerParser_traitsParser.parse_with pi oi parser input cursor ByteOrder.Big
      ⦃ result => Spec.satisfies (Spec.intRange child le parser.lower parser.upper cursor) result ⦄ := by
  rw [IntRange.Insts.RusthammerParser_traitsParser.parse_with]
  apply verify_spec (Shared0P.Insts.RusthammerParser_traitsParser pi)
    (ParserInputIntRangeT.parse_with.closure.Insts.CoreOpsFunctionFnTupleShared1TBool pi oi)
    { parser := parser.parser, predicate := parser } input cursor child
    (Spec.inRange le parser.lower parser.upper) hp
  intro next value _hvalue
  exact int_range_predicate_spec pi oi parser value le hle

theorem int_range_spec {P T : Type} (pi : parser_traits.Parser P T) (oi : core.cmp.Ord T)
    (parser : IntRange P T) (input : Slice U8) (cursor : Cursor)
    (child : Cursor → Spec.ParseResult T → Prop) (le : T → T → Prop) [DecidableRel le]
    (hp : pi.parse_with parser.parser input cursor ByteOrder.Big ⦃ result => Spec.satisfies (child cursor) result ⦄)
    (hle : ∀ a b, oi.partialOrdInst.le a b ⦃ result => result = decide (le a b) ⦄) :
    parser_traits.Parser.parse.default (IntRange.Insts.RusthammerParser_traitsParser pi oi) parser input cursor
      ⦃ result => Spec.intRange child le parser.lower parser.upper cursor result ⦄ := by
  exact complete_spec (IntRange.Insts.RusthammerParser_traitsParser pi oi) parser input cursor
    (Spec.intRange child le parser.lower parser.upper cursor)
    (int_range_final_spec pi oi parser input cursor child le hp hle)

/-- Successful ranges retain the child's exact cursor and value. -/
theorem int_range_success {T : Type} (child : Cursor → Spec.ParseResult T → Prop)
    (le : T → T → Prop) [DecidableRel le] (lower upper value : T) (cursor next : Cursor)
    (h : Contracts.verify child (Spec.inRange le lower upper) cursor (.Ok (next, value))) :
    child cursor (.Ok (next, value)) ∧ le lower value ∧ le value upper := by
  rcases h with ⟨parsed, hparsed, houtcome⟩
  cases parsed with
  | Err error => cases houtcome
  | Ok pair =>
    rcases pair with ⟨after, output⟩
    by_cases hbounds : Spec.inRange le lower upper output
    · simp only [if_pos hbounds, core.result.Result.Ok.injEq, Prod.mk.injEq] at houtcome
      rcases houtcome with ⟨rfl, rfl⟩
      exact ⟨hparsed, hbounds⟩
    · simp only [if_neg hbounds] at houtcome
      cases houtcome

/-- Native integer comparisons discharge the generic ordering hypotheses using
mathematical values, including the full unsigned range. -/
theorem int_range_u8_comparisons (a b : Std.U8) :
    (core.cmp.OrdU8.partialOrdInst.le a b ⦃ result => result = decide (a.val ≤ b.val) ⦄) ∧
    (core.cmp.OrdU8.partialOrdInst.gt a b ⦃ result => result = decide (¬ a.val ≤ b.val) ⦄) := by
  simp [core.cmp.impls.PartialOrdU8.le, core.cmp.impls.PartialOrdU8.gt, liftFun2, spec_ok, not_le]

theorem int_range_u16_comparisons (a b : Std.U16) :
    (core.cmp.OrdU16.partialOrdInst.le a b ⦃ result => result = decide (a.val ≤ b.val) ⦄) ∧
    (core.cmp.OrdU16.partialOrdInst.gt a b ⦃ result => result = decide (¬ a.val ≤ b.val) ⦄) := by
  simp [core.cmp.impls.PartialOrdU16.le, core.cmp.impls.PartialOrdU16.gt, liftFun2, spec_ok, not_le]

theorem int_range_u32_comparisons (a b : Std.U32) :
    (core.cmp.OrdU32.partialOrdInst.le a b ⦃ result => result = decide (a.val ≤ b.val) ⦄) ∧
    (core.cmp.OrdU32.partialOrdInst.gt a b ⦃ result => result = decide (¬ a.val ≤ b.val) ⦄) := by
  simp [core.cmp.impls.PartialOrdU32.le, core.cmp.impls.PartialOrdU32.gt, liftFun2, spec_ok, not_le]

theorem int_range_u64_comparisons (a b : Std.U64) :
    (core.cmp.OrdU64.partialOrdInst.le a b ⦃ result => result = decide (a.val ≤ b.val) ⦄) ∧
    (core.cmp.OrdU64.partialOrdInst.gt a b ⦃ result => result = decide (¬ a.val ≤ b.val) ⦄) := by
  simp [core.cmp.impls.PartialOrdU64.le, core.cmp.impls.PartialOrdU64.gt, liftFun2, spec_ok, not_le]

theorem int_range_i8_comparisons (a b : Std.I8) :
    (core.cmp.OrdI8.partialOrdInst.le a b ⦃ result => result = decide (a.val ≤ b.val) ⦄) ∧
    (core.cmp.OrdI8.partialOrdInst.gt a b ⦃ result => result = decide (¬ a.val ≤ b.val) ⦄) := by
  simp [core.cmp.impls.PartialOrdI8.le, core.cmp.impls.PartialOrdI8.gt, liftFun2, spec_ok, not_le]

theorem int_range_i16_comparisons (a b : Std.I16) :
    (core.cmp.OrdI16.partialOrdInst.le a b ⦃ result => result = decide (a.val ≤ b.val) ⦄) ∧
    (core.cmp.OrdI16.partialOrdInst.gt a b ⦃ result => result = decide (¬ a.val ≤ b.val) ⦄) := by
  simp [core.cmp.impls.PartialOrdI16.le, core.cmp.impls.PartialOrdI16.gt, liftFun2, spec_ok, not_le]

theorem int_range_i32_comparisons (a b : Std.I32) :
    (core.cmp.OrdI32.partialOrdInst.le a b ⦃ result => result = decide (a.val ≤ b.val) ⦄) ∧
    (core.cmp.OrdI32.partialOrdInst.gt a b ⦃ result => result = decide (¬ a.val ≤ b.val) ⦄) := by
  simp [core.cmp.impls.PartialOrdI32.le, core.cmp.impls.PartialOrdI32.gt, liftFun2, spec_ok, not_le]

theorem int_range_i64_comparisons (a b : Std.I64) :
    (core.cmp.OrdI64.partialOrdInst.le a b ⦃ result => result = decide (a.val ≤ b.val) ⦄) ∧
    (core.cmp.OrdI64.partialOrdInst.gt a b ⦃ result => result = decide (¬ a.val ≤ b.val) ⦄) := by
  simp [core.cmp.impls.PartialOrdI64.le, core.cmp.impls.PartialOrdI64.gt, liftFun2, spec_ok, not_le]

theorem int_range_u8_new_spec {P : Type} (pi : parser_traits.Parser P Std.U8)
    (child : P) (lower upper : Std.U8) :
    IntRange.new pi core.cmp.OrdU8 child lower upper
      ⦃ result => Spec.intRangeNewOutcome (fun a b => a.val ≤ b.val) child lower upper result ⦄ := by
  exact int_range_new_spec pi core.cmp.OrdU8 child lower upper
    (fun a b => a.val ≤ b.val) (int_range_u8_comparisons lower upper).2

theorem byte_integer_range_with_spec (parser : IntRange Code.grammar.numeric.Byte Std.U8)
    (input : Slice U8) (cursor : Cursor) :
    IntRange.Insts.RusthammerParser_traitsParser.parse_with Code.grammar.numeric.Byte.Insts.RusthammerParser_traitsParserInputU8 core.cmp.OrdU8
      parser input cursor ByteOrder.Big
      ⦃ result => Contracts.verify
        (fun start => Contracts.primitive (Spec.unsignedIntegerOutcome .U8 input start))
        (Spec.inRange (fun a b => a.val ≤ b.val) parser.lower parser.upper) cursor result ⦄ := by
  rcases parser with ⟨⟨⟩, lower, upper⟩
  exact int_range_with_spec Code.grammar.numeric.Byte.Insts.RusthammerParser_traitsParserInputU8 core.cmp.OrdU8
    { parser := (), lower, upper } input cursor ByteOrder.Big _ (fun a b => a.val ≤ b.val)
    (byte_integer_with_spec input cursor)
    (fun a b => (int_range_u8_comparisons a b).1)

theorem int_range_u16_new_spec {P : Type} (pi : parser_traits.Parser P Std.U16)
    (child : P) (lower upper : Std.U16) :
    IntRange.new pi core.cmp.OrdU16 child lower upper
      ⦃ result => Spec.intRangeNewOutcome (fun a b => a.val ≤ b.val) child lower upper result ⦄ := by
  exact int_range_new_spec pi core.cmp.OrdU16 child lower upper
    (fun a b => a.val ≤ b.val) (int_range_u16_comparisons lower upper).2

theorem be_u16_range_with_spec (parser : IntRange BeU16 Std.U16)
    (input : Slice U8) (cursor : Cursor) :
    IntRange.Insts.RusthammerParser_traitsParser.parse_with BeU16.Insts.RusthammerParser_traitsParserInputU16 core.cmp.OrdU16
      parser input cursor ByteOrder.Big
      ⦃ result => Contracts.verify
        (fun start => Contracts.primitive (Spec.unsignedIntegerOutcome .U16 input start))
        (Spec.inRange (fun a b => a.val ≤ b.val) parser.lower parser.upper) cursor result ⦄ := by
  rcases parser with ⟨⟨⟩, lower, upper⟩
  exact int_range_with_spec BeU16.Insts.RusthammerParser_traitsParserInputU16 core.cmp.OrdU16
    { parser := (), lower, upper } input cursor ByteOrder.Big _ (fun a b => a.val ≤ b.val)
    (be_u16_with_spec input cursor)
    (fun a b => (int_range_u16_comparisons a b).1)

theorem int_range_u32_new_spec {P : Type} (pi : parser_traits.Parser P Std.U32)
    (child : P) (lower upper : Std.U32) :
    IntRange.new pi core.cmp.OrdU32 child lower upper
      ⦃ result => Spec.intRangeNewOutcome (fun a b => a.val ≤ b.val) child lower upper result ⦄ := by
  exact int_range_new_spec pi core.cmp.OrdU32 child lower upper
    (fun a b => a.val ≤ b.val) (int_range_u32_comparisons lower upper).2

theorem be_u32_range_with_spec (parser : IntRange BeU32 Std.U32)
    (input : Slice U8) (cursor : Cursor) :
    IntRange.Insts.RusthammerParser_traitsParser.parse_with BeU32.Insts.RusthammerParser_traitsParserInputU32 core.cmp.OrdU32
      parser input cursor ByteOrder.Big
      ⦃ result => Contracts.verify
        (fun start => Contracts.primitive (Spec.unsignedIntegerOutcome .U32 input start))
        (Spec.inRange (fun a b => a.val ≤ b.val) parser.lower parser.upper) cursor result ⦄ := by
  rcases parser with ⟨⟨⟩, lower, upper⟩
  exact int_range_with_spec BeU32.Insts.RusthammerParser_traitsParserInputU32 core.cmp.OrdU32
    { parser := (), lower, upper } input cursor ByteOrder.Big _ (fun a b => a.val ≤ b.val)
    (be_u32_with_spec input cursor)
    (fun a b => (int_range_u32_comparisons a b).1)

theorem int_range_u64_new_spec {P : Type} (pi : parser_traits.Parser P Std.U64)
    (child : P) (lower upper : Std.U64) :
    IntRange.new pi core.cmp.OrdU64 child lower upper
      ⦃ result => Spec.intRangeNewOutcome (fun a b => a.val ≤ b.val) child lower upper result ⦄ := by
  exact int_range_new_spec pi core.cmp.OrdU64 child lower upper
    (fun a b => a.val ≤ b.val) (int_range_u64_comparisons lower upper).2

theorem be_u64_range_with_spec (parser : IntRange BeU64 Std.U64)
    (input : Slice U8) (cursor : Cursor) :
    IntRange.Insts.RusthammerParser_traitsParser.parse_with BeU64.Insts.RusthammerParser_traitsParserInputU64 core.cmp.OrdU64
      parser input cursor ByteOrder.Big
      ⦃ result => Contracts.verify
        (fun start => Contracts.primitive (Spec.unsignedIntegerOutcome .U64 input start))
        (Spec.inRange (fun a b => a.val ≤ b.val) parser.lower parser.upper) cursor result ⦄ := by
  rcases parser with ⟨⟨⟩, lower, upper⟩
  exact int_range_with_spec BeU64.Insts.RusthammerParser_traitsParserInputU64 core.cmp.OrdU64
    { parser := (), lower, upper } input cursor ByteOrder.Big _ (fun a b => a.val ≤ b.val)
    (be_u64_with_spec input cursor)
    (fun a b => (int_range_u64_comparisons a b).1)

theorem int_range_i8_new_spec {P : Type} (pi : parser_traits.Parser P Std.I8)
    (child : P) (lower upper : Std.I8) :
    IntRange.new pi core.cmp.OrdI8 child lower upper
      ⦃ result => Spec.intRangeNewOutcome (fun a b => a.val ≤ b.val) child lower upper result ⦄ := by
  exact int_range_new_spec pi core.cmp.OrdI8 child lower upper
    (fun a b => a.val ≤ b.val) (int_range_i8_comparisons lower upper).2

theorem i8_range_with_spec (parser : IntRange Code.grammar.numeric.I8 Std.I8)
    (input : Slice U8) (cursor : Cursor) :
    IntRange.Insts.RusthammerParser_traitsParser.parse_with Code.grammar.numeric.I8.Insts.RusthammerParser_traitsParserInputI8 core.cmp.OrdI8
      parser input cursor ByteOrder.Big
      ⦃ result => Contracts.verify
        (fun start => Contracts.primitive (Spec.signedIntegerOutcome .I8 input start))
        (Spec.inRange (fun a b => a.val ≤ b.val) parser.lower parser.upper) cursor result ⦄ := by
  rcases parser with ⟨⟨⟩, lower, upper⟩
  exact int_range_with_spec Code.grammar.numeric.I8.Insts.RusthammerParser_traitsParserInputI8 core.cmp.OrdI8
    { parser := (), lower, upper } input cursor ByteOrder.Big _ (fun a b => a.val ≤ b.val)
    (i8_with_spec input cursor)
    (fun a b => (int_range_i8_comparisons a b).1)

theorem int_range_i16_new_spec {P : Type} (pi : parser_traits.Parser P Std.I16)
    (child : P) (lower upper : Std.I16) :
    IntRange.new pi core.cmp.OrdI16 child lower upper
      ⦃ result => Spec.intRangeNewOutcome (fun a b => a.val ≤ b.val) child lower upper result ⦄ := by
  exact int_range_new_spec pi core.cmp.OrdI16 child lower upper
    (fun a b => a.val ≤ b.val) (int_range_i16_comparisons lower upper).2

theorem be_i16_range_with_spec (parser : IntRange BeI16 Std.I16)
    (input : Slice U8) (cursor : Cursor) :
    IntRange.Insts.RusthammerParser_traitsParser.parse_with BeI16.Insts.RusthammerParser_traitsParserInputI16 core.cmp.OrdI16
      parser input cursor ByteOrder.Big
      ⦃ result => Contracts.verify
        (fun start => Contracts.primitive (Spec.signedIntegerOutcome .I16 input start))
        (Spec.inRange (fun a b => a.val ≤ b.val) parser.lower parser.upper) cursor result ⦄ := by
  rcases parser with ⟨⟨⟩, lower, upper⟩
  exact int_range_with_spec BeI16.Insts.RusthammerParser_traitsParserInputI16 core.cmp.OrdI16
    { parser := (), lower, upper } input cursor ByteOrder.Big _ (fun a b => a.val ≤ b.val)
    (be_i16_with_spec input cursor)
    (fun a b => (int_range_i16_comparisons a b).1)

theorem int_range_i32_new_spec {P : Type} (pi : parser_traits.Parser P Std.I32)
    (child : P) (lower upper : Std.I32) :
    IntRange.new pi core.cmp.OrdI32 child lower upper
      ⦃ result => Spec.intRangeNewOutcome (fun a b => a.val ≤ b.val) child lower upper result ⦄ := by
  exact int_range_new_spec pi core.cmp.OrdI32 child lower upper
    (fun a b => a.val ≤ b.val) (int_range_i32_comparisons lower upper).2

theorem be_i32_range_with_spec (parser : IntRange BeI32 Std.I32)
    (input : Slice U8) (cursor : Cursor) :
    IntRange.Insts.RusthammerParser_traitsParser.parse_with BeI32.Insts.RusthammerParser_traitsParserInputI32 core.cmp.OrdI32
      parser input cursor ByteOrder.Big
      ⦃ result => Contracts.verify
        (fun start => Contracts.primitive (Spec.signedIntegerOutcome .I32 input start))
        (Spec.inRange (fun a b => a.val ≤ b.val) parser.lower parser.upper) cursor result ⦄ := by
  rcases parser with ⟨⟨⟩, lower, upper⟩
  exact int_range_with_spec BeI32.Insts.RusthammerParser_traitsParserInputI32 core.cmp.OrdI32
    { parser := (), lower, upper } input cursor ByteOrder.Big _ (fun a b => a.val ≤ b.val)
    (be_i32_with_spec input cursor)
    (fun a b => (int_range_i32_comparisons a b).1)

theorem int_range_i64_new_spec {P : Type} (pi : parser_traits.Parser P Std.I64)
    (child : P) (lower upper : Std.I64) :
    IntRange.new pi core.cmp.OrdI64 child lower upper
      ⦃ result => Spec.intRangeNewOutcome (fun a b => a.val ≤ b.val) child lower upper result ⦄ := by
  exact int_range_new_spec pi core.cmp.OrdI64 child lower upper
    (fun a b => a.val ≤ b.val) (int_range_i64_comparisons lower upper).2

theorem be_i64_range_with_spec (parser : IntRange BeI64 Std.I64)
    (input : Slice U8) (cursor : Cursor) :
    IntRange.Insts.RusthammerParser_traitsParser.parse_with BeI64.Insts.RusthammerParser_traitsParserInputI64 core.cmp.OrdI64
      parser input cursor ByteOrder.Big
      ⦃ result => Contracts.verify
        (fun start => Contracts.primitive (Spec.signedIntegerOutcome .I64 input start))
        (Spec.inRange (fun a b => a.val ≤ b.val) parser.lower parser.upper) cursor result ⦄ := by
  rcases parser with ⟨⟨⟩, lower, upper⟩
  exact int_range_with_spec BeI64.Insts.RusthammerParser_traitsParserInputI64 core.cmp.OrdI64
    { parser := (), lower, upper } input cursor ByteOrder.Big _ (fun a b => a.val ≤ b.val)
    (be_i64_with_spec input cursor)
    (fun a b => (int_range_i64_comparisons a b).1)

end RustHammer.Proofs
