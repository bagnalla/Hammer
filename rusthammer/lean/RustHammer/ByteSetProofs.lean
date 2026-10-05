import RustHammer.ByteSetBitmapProofs
import RustHammer.ByteProofs

open Aeneas Aeneas.Std Result WP

namespace RustHammer.Proofs
open Code

theorem byte_set_clone_spec (set : ByteSet) :
    ByteSet.Insts.CoreCloneClone.clone set ⦃ result => result = set ⦄ := by
  simp [ByteSet.Insts.CoreCloneClone.clone, spec_ok]

/-- Representation correctness connects bitmap-based parsing to the caller's
literal set without retaining its construction slice. -/
theorem bitmap_predicate_of_represents (set : ByteSet) (bytes : List U8)
    (excluded : Bool) (hrep : Spec.bitmapRepresents set bytes) :
    Spec.bitmapPredicate set excluded = Spec.byteSetPredicate bytes excluded := by
  funext value
  apply propext
  cases excluded <;> simp [Spec.bitmapPredicate, Spec.byteSetPredicate, hrep value]

theorem byte_in_new_spec (bytes : Slice U8) :
    ByteIn.new bytes ⦃ parser => Spec.bitmapRepresents parser.set bytes.val ⦄ := by
  unfold ByteIn.new
  step with byte_set_new_spec bytes
  assumption

theorem byte_in_clone_spec (parser : ByteIn) :
    ByteIn.Insts.CoreCloneClone.clone parser ⦃ result => result = parser ⦄ := by
  simp [ByteIn.Insts.CoreCloneClone.clone, spec_ok]

theorem byte_in_accepts_spec (parser : ByteIn) (value : U8) :
    ByteIn.accepts parser value
      ⦃ result => result = decide (Spec.bitmapPredicate parser.set false value) ⦄ := by
  exact byte_set_contains_spec parser.set value

theorem byte_in_predicate_spec (parser : ByteIn) (value : U8) :
    ParserInputByteInU8.parse_with.closure.Insts.CoreOpsFunctionFnTupleShared1U8Bool.call
      parser value ⦃ result => result = decide (Spec.bitmapPredicate parser.set false value) ⦄ := by
  exact byte_in_accepts_spec parser value

/-- This total contract applies to every bitmap, with no constructor hypothesis. -/
theorem byte_in_bitmap_with_spec (parser : ByteIn) (input : Slice U8)
    (cursor : Cursor) (status : InputStatus) :
    ByteIn.Insts.RusthammerParserInputU8.parse_with parser input cursor (Spec.defaultContext status)
      ⦃ result => Spec.bitmapOutcome input status parser.set false cursor result ⦄ := by
  unfold ByteIn.Insts.RusthammerParserInputU8.parse_with
  apply verify_with_spec Byte.Insts.RusthammerParserInputU8
    ParserInputByteInU8.parse_with.closure.Insts.CoreOpsFunctionFnTupleShared1U8Bool
    { parser := (), predicate := parser } input cursor (Spec.defaultContext status) _
    (Spec.bitmapPredicate parser.set false) (byte_with_spec input cursor status)
  intro next value _hvalue
  exact byte_in_predicate_spec parser value

/-- The constructor's representation theorem recovers literal-set semantics. -/
theorem byte_in_with_spec (parser : ByteIn) (bytes : List U8)
    (hrep : Spec.bitmapRepresents parser.set bytes) (input : Slice U8)
    (cursor : Cursor) (status : InputStatus) :
    ByteIn.Insts.RusthammerParserInputU8.parse_with parser input cursor (Spec.defaultContext status)
      ⦃ result => Spec.byteSetOutcome input status bytes false cursor result ⦄ := by
  simpa only [Spec.bitmapOutcome, bitmap_predicate_of_represents parser.set bytes false hrep] using
    byte_in_bitmap_with_spec parser input cursor status

theorem byte_in_final_spec (parser : ByteIn) (input : Slice U8) (cursor : Cursor) :
    ByteIn.Insts.RusthammerParserInputU8.parse_with parser input cursor ParseContext.FINAL
      ⦃ result => Spec.completed (Spec.bitmapComplete input parser.set false cursor) result ⦄ := by
  unfold ByteIn.Insts.RusthammerParserInputU8.parse_with
  apply verify_spec Byte.Insts.RusthammerParserInputU8
    ParserInputByteInU8.parse_with.closure.Insts.CoreOpsFunctionFnTupleShared1U8Bool
    { parser := (), predicate := parser } input cursor _
    (Spec.bitmapPredicate parser.set false)
  · simpa only [ParseContext.FINAL, Partial.primitive, Partial.primitiveResult, Spec.completed] using
      byte_with_spec input cursor .Final
  · intro next value _hvalue
    exact byte_in_predicate_spec parser value

theorem byte_in_spec (parser : ByteIn) (input : Slice U8) (cursor : Cursor) :
    Parser.parse.default ByteIn.Insts.RusthammerParserInputU8 parser input cursor
      ⦃ result => Spec.bitmapComplete input parser.set false cursor result ⦄ := by
  exact complete_spec ByteIn.Insts.RusthammerParserInputU8 parser input cursor
    (Spec.bitmapComplete input parser.set false cursor)
    (byte_in_final_spec parser input cursor)

theorem byte_in_set_spec (parser : ByteIn) (bytes : List U8)
    (hrep : Spec.bitmapRepresents parser.set bytes) (input : Slice U8) (cursor : Cursor) :
    Parser.parse.default ByteIn.Insts.RusthammerParserInputU8 parser input cursor
      ⦃ result => Spec.byteSetComplete input bytes false cursor result ⦄ := by
  simpa only [Spec.bitmapComplete, bitmap_predicate_of_represents parser.set bytes false hrep] using
    byte_in_spec parser input cursor

theorem byte_not_in_new_spec (bytes : Slice U8) :
    ByteNotIn.new bytes ⦃ parser => Spec.bitmapRepresents parser.set bytes.val ⦄ := by
  unfold ByteNotIn.new
  step with byte_set_new_spec bytes
  assumption

theorem byte_not_in_clone_spec (parser : ByteNotIn) :
    ByteNotIn.Insts.CoreCloneClone.clone parser ⦃ result => result = parser ⦄ := by
  simp [ByteNotIn.Insts.CoreCloneClone.clone, spec_ok]

theorem byte_not_in_accepts_spec (parser : ByteNotIn) (value : U8) :
    ByteNotIn.accepts parser value
      ⦃ result => result = decide (Spec.bitmapPredicate parser.set true value) ⦄ := by
  unfold ByteNotIn.accepts
  step with byte_set_contains_spec parser.set value as ⟨member, hmember⟩
  simp [hmember, Spec.bitmapPredicate]

theorem byte_not_in_predicate_spec (parser : ByteNotIn) (value : U8) :
    ParserInputByteNotInU8.parse_with.closure.Insts.CoreOpsFunctionFnTupleShared1U8Bool.call
      parser value ⦃ result => result = decide (Spec.bitmapPredicate parser.set true value) ⦄ := by
  exact byte_not_in_accepts_spec parser value

/-- This total contract applies to every bitmap, with no constructor hypothesis. -/
theorem byte_not_in_bitmap_with_spec (parser : ByteNotIn) (input : Slice U8)
    (cursor : Cursor) (status : InputStatus) :
    ByteNotIn.Insts.RusthammerParserInputU8.parse_with parser input cursor (Spec.defaultContext status)
      ⦃ result => Spec.bitmapOutcome input status parser.set true cursor result ⦄ := by
  unfold ByteNotIn.Insts.RusthammerParserInputU8.parse_with
  apply verify_with_spec Byte.Insts.RusthammerParserInputU8
    ParserInputByteNotInU8.parse_with.closure.Insts.CoreOpsFunctionFnTupleShared1U8Bool
    { parser := (), predicate := parser } input cursor (Spec.defaultContext status) _
    (Spec.bitmapPredicate parser.set true) (byte_with_spec input cursor status)
  intro next value _hvalue
  exact byte_not_in_predicate_spec parser value

/-- The constructor's representation theorem recovers literal-set semantics. -/
theorem byte_not_in_with_spec (parser : ByteNotIn) (bytes : List U8)
    (hrep : Spec.bitmapRepresents parser.set bytes) (input : Slice U8)
    (cursor : Cursor) (status : InputStatus) :
    ByteNotIn.Insts.RusthammerParserInputU8.parse_with parser input cursor (Spec.defaultContext status)
      ⦃ result => Spec.byteSetOutcome input status bytes true cursor result ⦄ := by
  simpa only [Spec.bitmapOutcome, bitmap_predicate_of_represents parser.set bytes true hrep] using
    byte_not_in_bitmap_with_spec parser input cursor status

theorem byte_not_in_final_spec (parser : ByteNotIn) (input : Slice U8) (cursor : Cursor) :
    ByteNotIn.Insts.RusthammerParserInputU8.parse_with parser input cursor ParseContext.FINAL
      ⦃ result => Spec.completed (Spec.bitmapComplete input parser.set true cursor) result ⦄ := by
  unfold ByteNotIn.Insts.RusthammerParserInputU8.parse_with
  apply verify_spec Byte.Insts.RusthammerParserInputU8
    ParserInputByteNotInU8.parse_with.closure.Insts.CoreOpsFunctionFnTupleShared1U8Bool
    { parser := (), predicate := parser } input cursor _
    (Spec.bitmapPredicate parser.set true)
  · simpa only [ParseContext.FINAL, Partial.primitive, Partial.primitiveResult, Spec.completed] using
      byte_with_spec input cursor .Final
  · intro next value _hvalue
    exact byte_not_in_predicate_spec parser value

theorem byte_not_in_spec (parser : ByteNotIn) (input : Slice U8) (cursor : Cursor) :
    Parser.parse.default ByteNotIn.Insts.RusthammerParserInputU8 parser input cursor
      ⦃ result => Spec.bitmapComplete input parser.set true cursor result ⦄ := by
  exact complete_spec ByteNotIn.Insts.RusthammerParserInputU8 parser input cursor
    (Spec.bitmapComplete input parser.set true cursor)
    (byte_not_in_final_spec parser input cursor)

theorem byte_not_in_set_spec (parser : ByteNotIn) (bytes : List U8)
    (hrep : Spec.bitmapRepresents parser.set bytes) (input : Slice U8) (cursor : Cursor) :
    Parser.parse.default ByteNotIn.Insts.RusthammerParserInputU8 parser input cursor
      ⦃ result => Spec.byteSetComplete input bytes true cursor result ⦄ := by
  simpa only [Spec.bitmapComplete, bitmap_predicate_of_represents parser.set bytes true hrep] using
    byte_not_in_spec parser input cursor

/-- Successful parsing consumes exactly eight bits, returns their decoded value,
and satisfies the requested membership or exclusion predicate. -/
theorem byte_set_success (input : Slice U8) (status : InputStatus)
    (bytes : List U8) (excluded : Bool) (cursor next : Cursor) (value : U8)
    (h : Spec.byteSetOutcome input status bytes excluded cursor (.Success next value)) :
    Spec.validCursor input cursor ∧ Spec.validCursor input next ∧
      Spec.position next = Spec.position cursor + 8 ∧
      value.val = Spec.unsignedBits input (Spec.position cursor) 8 ∧
      Spec.byteSetPredicate bytes excluded value := by
  rcases h with ⟨parsed, hparsed, houtcome⟩
  cases parsed with
  | NeedMore => cases houtcome
  | Error error => cases houtcome
  | Success after output =>
    by_cases hmember : Spec.byteSetPredicate bytes excluded output
    · simp only [if_pos hmember, ParseOutcome.Success.injEq] at houtcome
      rcases houtcome with ⟨rfl, rfl⟩
      rcases byte_success input cursor next value status hparsed with ⟨hc, hn, hp, hv⟩
      exact ⟨hc, hn, hp, hv, hmember⟩
    · simp only [if_neg hmember] at houtcome
      cases houtcome

/-- Any two lists denoting the same set give the same parsing contract,
regardless of list length, ordering, or duplicates. -/
theorem byte_set_membership_ext (input : Slice U8) (status : InputStatus)
    (left right : List U8) (excluded : Bool) (cursor : Cursor) (outcome : ParseOutcome U8)
    (hmembers : ∀ value, value ∈ left ↔ value ∈ right) :
    Spec.byteSetOutcome input status left excluded cursor outcome ↔
      Spec.byteSetOutcome input status right excluded cursor outcome := by
  have hpred : Spec.byteSetPredicate left excluded = Spec.byteSetPredicate right excluded := by
    funext value
    apply propext
    cases excluded <;> simp [Spec.byteSetPredicate, hmembers value]
  simp only [Spec.byteSetOutcome, hpred]

end RustHammer.Proofs
