import RustHammer.ByteSetBitmapProofs
import RustHammer.ByteProofs

open RustHammer.Code.grammar.bytes
  RustHammer.Code.grammar.numeric
  RustHammer.Code.input_types

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

end RustHammer.Proofs

namespace RustHammer.Ordering
open Code Proofs

theorem byte_in_with_spec (parser : ByteIn) (input : Slice U8) (cursor : Cursor)
    (context : ByteOrder) :
    ByteIn.Insts.RusthammerParser_traitsParserInputU8.parse_with parser input cursor context
      ⦃ result => Spec.verify
        (fun start => unsignedIntegerOutcome .U8 input start context)
        (Spec.bitmapPredicate parser.set false) cursor result ⦄ := by
  rw [ByteIn.Insts.RusthammerParser_traitsParserInputU8.parse_with]
  apply verify_with_spec Code.grammar.numeric.Byte.Insts.RusthammerParser_traitsParserInputU8
    ParserInputByteInU8.parse_with.closure.Insts.CoreOpsFunctionFnTupleShared1U8Bool
    { parser := (), predicate := parser } input cursor context _
    (Spec.bitmapPredicate parser.set false) (by
      simpa only [Code.grammar.numeric.Byte.Insts.RusthammerParser_traitsParserInputU8.parse_with] using
        byte_with_spec input cursor context)
  intro next value _
  exact byte_in_predicate_spec parser value

end RustHammer.Ordering

namespace RustHammer.Proofs
open Code

/-- This total contract applies to every bitmap, with no constructor hypothesis. -/
theorem byte_in_bitmap_with_spec (parser : ByteIn) (input : Slice U8)
    (cursor : Cursor) :
    ByteIn.Insts.RusthammerParser_traitsParserInputU8.parse_with parser input cursor ByteOrder.Big
      ⦃ result => Spec.bitmapOutcome input parser.set false cursor result ⦄ := by
  simpa only [Spec.bitmapOutcome, Spec.verify, Ordering.byte_outcome_default] using
    Ordering.byte_in_with_spec parser input cursor .Big

/-- The constructor's representation theorem recovers literal-set semantics. -/
theorem byte_in_with_spec (parser : ByteIn) (bytes : List U8)
    (hrep : Spec.bitmapRepresents parser.set bytes) (input : Slice U8)
    (cursor : Cursor) :
    ByteIn.Insts.RusthammerParser_traitsParserInputU8.parse_with parser input cursor ByteOrder.Big
      ⦃ result => Spec.byteSetOutcome input bytes false cursor result ⦄ := by
  simpa only [Spec.bitmapOutcome, bitmap_predicate_of_represents parser.set bytes false hrep] using
    byte_in_bitmap_with_spec parser input cursor

theorem byte_in_final_spec (parser : ByteIn) (input : Slice U8) (cursor : Cursor) :
    ByteIn.Insts.RusthammerParser_traitsParserInputU8.parse_with parser input cursor ByteOrder.Big
      ⦃ result => Spec.bitmapOutcome input parser.set false cursor result ⦄ := by
  exact byte_in_bitmap_with_spec parser input cursor

theorem byte_in_spec (parser : ByteIn) (input : Slice U8) (cursor : Cursor) :
    parser_traits.Parser.parse.default ByteIn.Insts.RusthammerParser_traitsParserInputU8 parser input cursor
      ⦃ result => Spec.bitmapOutcome input parser.set false cursor result ⦄ := by
  exact complete_spec ByteIn.Insts.RusthammerParser_traitsParserInputU8 parser input cursor
    (Spec.bitmapOutcome input parser.set false cursor)
    (byte_in_final_spec parser input cursor)

theorem byte_in_set_spec (parser : ByteIn) (bytes : List U8)
    (hrep : Spec.bitmapRepresents parser.set bytes) (input : Slice U8) (cursor : Cursor) :
    parser_traits.Parser.parse.default ByteIn.Insts.RusthammerParser_traitsParserInputU8 parser input cursor
      ⦃ result => Spec.byteSetOutcome input bytes false cursor result ⦄ := by
  simpa only [Spec.bitmapOutcome, bitmap_predicate_of_represents parser.set bytes false hrep] using
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

end RustHammer.Proofs

namespace RustHammer.Ordering
open Code Proofs

theorem byte_not_in_with_spec (parser : ByteNotIn) (input : Slice U8) (cursor : Cursor)
    (context : ByteOrder) :
    ByteNotIn.Insts.RusthammerParser_traitsParserInputU8.parse_with parser input cursor context
      ⦃ result => Spec.verify
        (fun start => unsignedIntegerOutcome .U8 input start context)
        (Spec.bitmapPredicate parser.set true) cursor result ⦄ := by
  rw [ByteNotIn.Insts.RusthammerParser_traitsParserInputU8.parse_with]
  apply verify_with_spec Code.grammar.numeric.Byte.Insts.RusthammerParser_traitsParserInputU8
    ParserInputByteNotInU8.parse_with.closure.Insts.CoreOpsFunctionFnTupleShared1U8Bool
    { parser := (), predicate := parser } input cursor context _
    (Spec.bitmapPredicate parser.set true) (by
      simpa only [Code.grammar.numeric.Byte.Insts.RusthammerParser_traitsParserInputU8.parse_with] using
        byte_with_spec input cursor context)
  intro next value _
  exact byte_not_in_predicate_spec parser value

end RustHammer.Ordering

namespace RustHammer.Proofs
open Code

/-- This total contract applies to every bitmap, with no constructor hypothesis. -/
theorem byte_not_in_bitmap_with_spec (parser : ByteNotIn) (input : Slice U8)
    (cursor : Cursor) :
    ByteNotIn.Insts.RusthammerParser_traitsParserInputU8.parse_with parser input cursor ByteOrder.Big
      ⦃ result => Spec.bitmapOutcome input parser.set true cursor result ⦄ := by
  simpa only [Spec.bitmapOutcome, Spec.verify, Ordering.byte_outcome_default] using
    Ordering.byte_not_in_with_spec parser input cursor .Big

/-- The constructor's representation theorem recovers literal-set semantics. -/
theorem byte_not_in_with_spec (parser : ByteNotIn) (bytes : List U8)
    (hrep : Spec.bitmapRepresents parser.set bytes) (input : Slice U8)
    (cursor : Cursor) :
    ByteNotIn.Insts.RusthammerParser_traitsParserInputU8.parse_with parser input cursor ByteOrder.Big
      ⦃ result => Spec.byteSetOutcome input bytes true cursor result ⦄ := by
  simpa only [Spec.bitmapOutcome, bitmap_predicate_of_represents parser.set bytes true hrep] using
    byte_not_in_bitmap_with_spec parser input cursor

theorem byte_not_in_final_spec (parser : ByteNotIn) (input : Slice U8) (cursor : Cursor) :
    ByteNotIn.Insts.RusthammerParser_traitsParserInputU8.parse_with parser input cursor ByteOrder.Big
      ⦃ result => Spec.bitmapOutcome input parser.set true cursor result ⦄ := by
  exact byte_not_in_bitmap_with_spec parser input cursor

theorem byte_not_in_spec (parser : ByteNotIn) (input : Slice U8) (cursor : Cursor) :
    parser_traits.Parser.parse.default ByteNotIn.Insts.RusthammerParser_traitsParserInputU8 parser input cursor
      ⦃ result => Spec.bitmapOutcome input parser.set true cursor result ⦄ := by
  exact complete_spec ByteNotIn.Insts.RusthammerParser_traitsParserInputU8 parser input cursor
    (Spec.bitmapOutcome input parser.set true cursor)
    (byte_not_in_final_spec parser input cursor)

theorem byte_not_in_set_spec (parser : ByteNotIn) (bytes : List U8)
    (hrep : Spec.bitmapRepresents parser.set bytes) (input : Slice U8) (cursor : Cursor) :
    parser_traits.Parser.parse.default ByteNotIn.Insts.RusthammerParser_traitsParserInputU8 parser input cursor
      ⦃ result => Spec.byteSetOutcome input bytes true cursor result ⦄ := by
  simpa only [Spec.bitmapOutcome, bitmap_predicate_of_represents parser.set bytes true hrep] using
    byte_not_in_spec parser input cursor

/-- Successful parsing consumes exactly eight bits, returns their decoded value,
and satisfies the requested membership or exclusion predicate. -/
theorem byte_set_success (input : Slice U8)
    (bytes : List U8) (excluded : Bool) (cursor next : Cursor) (value : U8)
    (h : Spec.byteSetOutcome input bytes excluded cursor (.Ok (next, value))) :
    Spec.validCursor input cursor ∧ Spec.validCursor input next ∧
      Spec.position next = Spec.position cursor + 8 ∧
      value.val = Spec.unsignedBits input (Spec.position cursor) 8 ∧
      Spec.byteSetPredicate bytes excluded value := by
  rcases h with ⟨parsed, hparsed, houtcome⟩
  cases parsed with
  | Err error => cases houtcome
  | Ok pair =>
    rcases pair with ⟨after, output⟩
    by_cases hmember : Spec.byteSetPredicate bytes excluded output
    · simp only [if_pos hmember, core.result.Result.Ok.injEq, Prod.mk.injEq] at houtcome
      rcases houtcome with ⟨rfl, rfl⟩
      rcases byte_success input cursor next value hparsed with ⟨hc, hn, hp, hv⟩
      exact ⟨hc, hn, hp, hv, hmember⟩
    · simp only [if_neg hmember] at houtcome
      cases houtcome

/-- Any two lists denoting the same set give the same parsing contract,
regardless of list length, ordering, or duplicates. -/
theorem byte_set_membership_ext (input : Slice U8)
    (left right : List U8) (excluded : Bool) (cursor : Cursor) (outcome : Spec.ParseResult U8)
    (hmembers : ∀ value, value ∈ left ↔ value ∈ right) :
    Spec.byteSetOutcome input left excluded cursor outcome ↔
      Spec.byteSetOutcome input right excluded cursor outcome := by
  have hpred : Spec.byteSetPredicate left excluded = Spec.byteSetPredicate right excluded := by
    funext value
    apply propext
    cases excluded <;> simp [Spec.byteSetPredicate, hmembers value]
  simp only [Spec.byteSetOutcome, hpred]

end RustHammer.Proofs
