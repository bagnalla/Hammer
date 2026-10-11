import RustHammer.ByteSpec
import RustHammer.ParserProofs

open RustHammer.Code.grammar.bytes
  RustHammer.Code.grammar.numeric
  RustHammer.Code.input_types

open Aeneas Aeneas.Std Result WP

namespace RustHammer.Proofs
open Code

/-- The narrowing cast is lossless: eight decoded bits are strictly below 256. -/
theorem byte_with_spec (input : Slice U8) (cursor : Cursor) :
    Code.grammar.numeric.Byte.Insts.RusthammerParser_traitsParserInputU8.parse_with () input cursor ByteOrder.Big
      ⦃ result => Contracts.primitive (Spec.byteOutcome input cursor) result ⦄ := by
  rw [Code.grammar.numeric.Byte.Insts.RusthammerParser_traitsParserInputU8.parse_with]
  step with bits_with_spec { width := 8#u8 } input cursor (by decide) as ⟨outcome, houtcome⟩
  rcases houtcome with ⟨parsed, hparsed, heq⟩
  subst outcome
  by_cases hvalid : Spec.validCursor input cursor
  · by_cases hfit : Spec.position cursor + 8 ≤ 8 * input.val.length
    · simp only [Spec.bitsOutcome, if_pos hvalid, UScalar.ofNatCore_val_eq, if_pos hfit] at hparsed
      rcases hparsed with ⟨next, value, rfl, hnext, hpos, hvalue⟩

      have hbound := unsignedBits_lt_pow input (Spec.position cursor) 8
      step with UScalar.cast_inBounds_spec .U8 value (by scalar_tac) as ⟨byte, hbyte⟩
      refine ⟨.Ok (next, byte), ?_, rfl⟩
      simp only [Spec.byteOutcome, if_pos hvalid, if_pos hfit]
      exact ⟨next, byte, rfl, hnext, hpos, by simpa only [hbyte, UScalar.ofNatCore_val_eq] using hvalue⟩
    · have heq : parsed = .Err .UnexpectedEnd := by
        simpa only [Spec.bitsOutcome, if_pos hvalid, UScalar.ofNatCore_val_eq, if_neg hfit] using hparsed
      subst parsed
      simp only [spec_ok]
      all_goals exact ⟨.Err .UnexpectedEnd, by simp only [Spec.byteOutcome, if_pos hvalid, if_neg hfit], rfl⟩
  · have heq : parsed = .Err .InvalidCursor := by
      simpa only [Spec.bitsOutcome, if_neg hvalid] using hparsed
    subst parsed
    simp only [spec_ok]
    all_goals exact ⟨.Err .InvalidCursor, by simp only [Spec.byteOutcome, if_neg hvalid], rfl⟩

theorem byte_spec (input : Slice U8) (cursor : Cursor) :
    parser_traits.Parser.parse.default Code.grammar.numeric.Byte.Insts.RusthammerParser_traitsParserInputU8 () input cursor
      ⦃ result => Spec.byteOutcome input cursor result ⦄ := by
  apply complete_spec
  simpa only [Code.grammar.numeric.Byte.Insts.RusthammerParser_traitsParserInputU8.parse_with, ByteOrder.Big,
    Contracts.primitive, Spec.satisfies] using
    byte_with_spec input cursor

theorem byte_pattern_new_spec (pattern : Slice U8) :
    BytePattern.new pattern ⦃ parser => parser.pattern = pattern ⦄ := by
  simp [BytePattern.new, spec_ok]

theorem byte_pattern_pattern_spec (parser : BytePattern) :
    BytePattern.impl.pattern parser ⦃ pattern => pattern = parser.pattern ⦄ := by
  simp [BytePattern.impl.pattern, spec_ok]

/-- The loop terminates by the remaining pattern length. Its continuation
invariant relates the remaining suffix to the entire mathematical pattern. -/
theorem match_byte_pattern_spec (pattern input : Slice U8) (cursor : Cursor) :
    grammar.bytes.match_byte_pattern pattern input cursor ByteOrder.Big
      ⦃ result => Spec.matchBytes input pattern.val cursor result ⦄ := by
  rw [grammar.bytes.match_byte_pattern]
  unfold match_byte_pattern_loop
  apply loop.spec_decr_nat (fun state => pattern.val.length - state.2.val)
    (fun (next, index) => index.val ≤ pattern.val.length ∧
      ∀ outcome, Spec.matchBytes input (pattern.val.drop index.val) next outcome →
        Spec.matchBytes input pattern.val cursor outcome)
  · rintro ⟨next, index⟩ ⟨hindex, hcont⟩
    unfold match_byte_pattern_loop.body

    by_cases hlt : index < pattern.len
    · have hlen : index.val < pattern.val.length := by scalar_tac
      have hdrop : pattern.val.drop index.val =
          pattern.val[index.val] :: pattern.val.drop (index.val + 1) := by
        exact List.drop_eq_getElem_cons hlen
      simp only [hlt, ↓reduceIte]
      step with byte_with_spec input next as ⟨decoded, hdecoded⟩
      cases decoded with
      | Err error =>
        simp only [spec_ok]
        apply hcont
        rw [hdrop]
        exact ⟨.Err error, hdecoded, rfl⟩
      | Ok pair =>
        rcases pair with ⟨after, value⟩
        step as ⟨expected, hexpected⟩
        by_cases heq : value = expected
        · simp only [heq, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
          step as ⟨following, hfollowing⟩
          refine ⟨by omega, ?_, by omega⟩
          intro outcome htail
          apply hcont
          rw [hdrop]
          refine ⟨.Ok (after, value), hdecoded, ?_⟩
          have hvalue : value = pattern.val[index.val] := by simpa [heq] using hexpected
          simpa only [hvalue, ↓reduceIte, hfollowing] using htail
        · simp only [bne_iff_ne, ne_eq, heq, not_false_eq_true, ↓reduceIte, spec_ok]
          apply hcont
          rw [hdrop]
          refine ⟨.Ok (after, value), hdecoded, ?_⟩
          have hvalue : value ≠ pattern.val[index.val] := by simpa [hexpected] using heq
          simp [hvalue]
    · have hend : index.val = pattern.val.length := by scalar_tac
      simp only [hlt, ↓reduceIte, spec_ok]
      apply hcont
      simp [hend, Spec.matchBytes]
  · simp

theorem byte_pattern_with_spec (parser : BytePattern) (input : Slice U8)
    (cursor : Cursor) :
    BytePattern.Insts.RusthammerParser_traitsParserInputSharedPatternSliceU8.parse_with parser input cursor ByteOrder.Big
      ⦃ result => Spec.bytePatternOutcome input parser.pattern cursor result ⦄ := by
  rw [BytePattern.Insts.RusthammerParser_traitsParserInputSharedPatternSliceU8.parse_with]
  step with match_byte_pattern_spec parser.pattern input cursor as ⟨outcome, houtcome⟩
  cases outcome with
  | Ok pair =>
    rcases pair with ⟨next, value⟩
    cases value
    simp only [Spec.bytePatternOutcome]
    exact ⟨rfl, houtcome⟩
  | Err error =>
    simpa only [spec_ok, Spec.bytePatternOutcome] using houtcome

private theorem primitive_success {α : Type}
    (contract : Spec.ParseResult α → Prop) (next : Cursor) (value : α)
    (h : Contracts.primitive contract (.Ok (next, value))) : contract (.Ok (next, value)) := by
  rcases h with ⟨parsed, hparsed, heq⟩
  cases parsed with
  | Ok pair => cases pair; simp_all []
  | Err error => cases error <;> simp_all []

theorem byte_success (input : Slice U8) (cursor next : Cursor) (value : U8)
    (h : Contracts.primitive (Spec.byteOutcome input cursor) (.Ok (next, value))) :
    Spec.validCursor input cursor ∧ Spec.validCursor input next ∧
      Spec.position next = Spec.position cursor + 8 ∧
      value.val = Spec.unsignedBits input (Spec.position cursor) 8 := by
  have hraw := primitive_success _ next value h
  unfold Spec.byteOutcome at hraw
  split at hraw
  · rename_i hvalid
    split at hraw
    · rcases hraw with ⟨after, byte, heq, hn, hp, hv⟩
      cases heq
      exact ⟨hvalid, hn, hp, hv⟩
    · cases hraw
  · cases hraw

/-- A matched pattern consumes exactly eight bits per byte and every output
byte equals the corresponding mathematical field of the input. -/
theorem match_bytes_success (input : Slice U8) (bytes : List U8)
    (cursor next : Cursor) (h : Spec.matchBytes input bytes cursor (.Ok (next, ()))) :
    Spec.position next = Spec.position cursor + 8 * bytes.length ∧
      ∀ i (hi : i < bytes.length),
        bytes[i].val = Spec.unsignedBits input (Spec.position cursor + 8 * i) 8 := by
  induction bytes generalizing cursor with
  | nil =>
    simp only [Spec.matchBytes, core.result.Result.Ok.injEq, Prod.mk.injEq, and_true] at h
    subst next
    simp
  | cons expected rest ih =>
    rcases h with ⟨decoded, hdecoded, hrest⟩
    cases decoded with
    | Err error => cases hrest
    | Ok pair =>
      rcases pair with ⟨middle, value⟩
      by_cases heq : value = expected
      · simp only [if_pos heq] at hrest
        have hbyte := byte_success input cursor middle value hdecoded
        obtain ⟨hpos, hvalues⟩ := ih middle hrest
        constructor
        · simp only [List.length_cons]
          omega
        · intro i hi
          cases i with
          | zero => simpa [heq] using hbyte.2.2.2
          | succ i =>
            have htail := hvalues i (by simpa using hi)
            simp only [List.getElem_cons_succ]
            have hposition : Spec.position middle + 8 * i = Spec.position cursor + 8 * (i + 1) := by omega
            simpa only [hposition] using htail
      · simp only [if_neg heq] at hrest
        cases hrest

theorem byte_pattern_success (input : Slice U8) (pattern output : Slice U8)
    (cursor next : Cursor) (h : Spec.bytePatternOutcome input pattern cursor (.Ok (next, output))) :
    output = pattern ∧ Spec.position next = Spec.position cursor + 8 * pattern.val.length ∧
      ∀ i (hi : i < pattern.val.length),
        pattern.val[i].val = Spec.unsignedBits input (Spec.position cursor + 8 * i) 8 := by
  exact ⟨h.1, match_bytes_success input pattern.val cursor next h.2⟩

/-- The default byte order preserves the pattern contract, including empty patterns. -/
theorem byte_pattern_final_spec (parser : BytePattern) (input : Slice U8) (cursor : Cursor) :
    BytePattern.Insts.RusthammerParser_traitsParserInputSharedPatternSliceU8.parse_with parser input cursor ByteOrder.Big
      ⦃ result => Spec.satisfies (Spec.bytePatternComplete input parser.pattern cursor) result ⦄ := by

  step with byte_pattern_with_spec parser input cursor as ⟨outcome, houtcome⟩
  cases outcome with
  | Ok pair =>
    rcases pair with ⟨next, output⟩
    exact ⟨.Ok (next, output), houtcome, rfl⟩
  | Err error => exact ⟨.Err error, houtcome, rfl⟩
theorem byte_pattern_spec (parser : BytePattern) (input : Slice U8) (cursor : Cursor) :
    parser_traits.Parser.parse.default BytePattern.Insts.RusthammerParser_traitsParserInputSharedPatternSliceU8 parser input cursor
      ⦃ result => Spec.bytePatternComplete input parser.pattern cursor result ⦄ := by
  exact complete_spec BytePattern.Insts.RusthammerParser_traitsParserInputSharedPatternSliceU8 parser input cursor
    (Spec.bytePatternComplete input parser.pattern cursor) (byte_pattern_final_spec parser input cursor)

end RustHammer.Proofs
