import RustHammer.ByteSpec
import RustHammer.PartialProofs

open RustHammer.Code.grammar.bytes
  RustHammer.Code.grammar.numeric
  RustHammer.Code.input_types

open Aeneas Aeneas.Std Result WP

namespace RustHammer.Proofs
open Code

private theorem primitive_ok {α : Type} (status : InputStatus) (next : Cursor) (value : α) :
    Partial.primitiveResult status (.Ok (next, value)) = .Success next value := by
  cases status <;> rfl

/-- The narrowing cast is lossless: eight decoded bits are strictly below 256. -/
theorem byte_with_spec (input : Slice U8) (cursor : Cursor) (status : InputStatus) :
    Code.grammar.numeric.Byte.Insts.RusthammerParserInputU8.parse_with () input cursor (Spec.defaultContext status)
      ⦃ result => Partial.primitive status (Spec.byteOutcome input cursor) result ⦄ := by
  rw [Code.grammar.numeric.Byte.Insts.RusthammerParserInputU8.parse_with_eq]
  step with bits_with_spec { width := 8#u8 } input cursor status (by decide) as ⟨outcome, houtcome⟩
  rcases houtcome with ⟨parsed, hparsed, rfl⟩
  by_cases hvalid : Spec.validCursor input cursor
  · by_cases hfit : Spec.position cursor + 8 ≤ 8 * input.val.length
    · simp only [Spec.bitsOutcome, if_pos hvalid, UScalar.ofNatCore_val_eq, if_pos hfit] at hparsed
      rcases hparsed with ⟨next, value, rfl, hnext, hpos, hvalue⟩
      rw [primitive_ok]
      have hbound := unsignedBits_lt_pow input (Spec.position cursor) 8
      step with UScalar.cast_inBounds_spec .U8 value (by scalar_tac) as ⟨byte, hbyte⟩
      refine ⟨.Ok (next, byte), ?_, (primitive_ok status next byte).symm⟩
      simp only [Spec.byteOutcome, if_pos hvalid, if_pos hfit]
      exact ⟨next, byte, rfl, hnext, hpos, by simpa only [hbyte, UScalar.ofNatCore_val_eq] using hvalue⟩
    · have heq : parsed = .Err .UnexpectedEnd := by
        simpa only [Spec.bitsOutcome, if_pos hvalid, UScalar.ofNatCore_val_eq, if_neg hfit] using hparsed
      subst parsed
      cases status <;> simp only [Partial.primitiveResult, Spec.completedResult, spec_ok]
      all_goals exact ⟨.Err .UnexpectedEnd, by simp only [Spec.byteOutcome, if_pos hvalid, if_neg hfit], rfl⟩
  · have heq : parsed = .Err .InvalidCursor := by
      simpa only [Spec.bitsOutcome, if_neg hvalid] using hparsed
    subst parsed
    cases status <;> simp only [Partial.primitiveResult, Spec.completedResult, spec_ok]
    all_goals exact ⟨.Err .InvalidCursor, by simp only [Spec.byteOutcome, if_neg hvalid], rfl⟩

theorem byte_spec (input : Slice U8) (cursor : Cursor) :
    DirectParser.parse Code.grammar.numeric.Byte.Insts.RusthammerParserInputU8 () input cursor
      ⦃ result => Spec.byteOutcome input cursor result ⦄ := by
  apply complete_spec
  simpa only [Code.grammar.numeric.Byte.Insts.RusthammerParserInputU8.parse_with, ParseContext.FINAL,
    Spec.defaultContext, Partial.primitive, Partial.primitiveResult, Spec.completed] using
    byte_with_spec input cursor .Final

theorem byte_pattern_new_spec (pattern : Slice U8) :
    BytePattern.new pattern ⦃ parser => parser.pattern = pattern ⦄ := by
  simp [BytePattern.new, spec_ok]

theorem byte_pattern_pattern_spec (parser : BytePattern) :
    BytePattern.impl.pattern parser ⦃ pattern => pattern = parser.pattern ⦄ := by
  simp [BytePattern.impl.pattern, spec_ok]

/-- The loop terminates by the remaining pattern length. Its continuation
invariant relates the remaining suffix to the entire mathematical pattern. -/
theorem match_byte_pattern_spec (pattern input : Slice U8) (cursor : Cursor) (status : InputStatus) :
    DirectRun.match_byte_pattern pattern input cursor (Spec.defaultContext status)
      ⦃ result => Spec.matchBytes input status pattern.val cursor result ⦄ := by
  rw [DirectRun.match_byte_pattern_eq]
  unfold DirectRun.match_byte_pattern_loop
  apply direct_projection_spec
  unfold match_byte_pattern_loop
  apply loop.spec_decr_nat (fun state => pattern.val.length - state.2.2.val)
    (fun (_, next, index) => index.val ≤ pattern.val.length ∧
      ∀ outcome, Spec.matchBytes input status (pattern.val.drop index.val) next outcome →
        Spec.matchBytes input status pattern.val cursor outcome)
  · rintro ⟨⟨⟩, next, index⟩ ⟨hindex, hcont⟩
    unfold match_byte_pattern_loop.body
    simp only [Code.grammar.numeric.Byte.Insts.RusthammerParserInputU8.parse_with_lift, Std.bind_assoc, bind_ok]
    by_cases hlt : index < pattern.len
    · have hlen : index.val < pattern.val.length := by scalar_tac
      have hdrop : pattern.val.drop index.val =
          pattern.val[index.val] :: pattern.val.drop (index.val + 1) := by
        exact List.drop_eq_getElem_cons hlen
      simp only [hlt, ↓reduceIte]
      step with byte_with_spec input next status as ⟨decoded, hdecoded⟩
      cases decoded with
      | NeedMore =>
        simp only [spec_ok]
        apply hcont
        rw [hdrop]
        exact ⟨.NeedMore, hdecoded, rfl⟩
      | Error error =>
        simp only [spec_ok]
        apply hcont
        rw [hdrop]
        exact ⟨.Error error, hdecoded, rfl⟩
      | Success after value =>
        step as ⟨expected, hexpected⟩
        by_cases heq : value = expected
        · simp only [heq, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
          step as ⟨following, hfollowing⟩
          refine ⟨by omega, ?_, by omega⟩
          intro outcome htail
          apply hcont
          rw [hdrop]
          refine ⟨.Success after value, hdecoded, ?_⟩
          have hvalue : value = pattern.val[index.val] := by simpa [heq] using hexpected
          simpa only [hvalue, ↓reduceIte, hfollowing] using htail
        · simp only [bne_iff_ne, ne_eq, heq, not_false_eq_true, ↓reduceIte, spec_ok]
          apply hcont
          rw [hdrop]
          refine ⟨.Success after value, hdecoded, ?_⟩
          have hvalue : value ≠ pattern.val[index.val] := by simpa [hexpected] using heq
          simp [hvalue]
    · have hend : index.val = pattern.val.length := by scalar_tac
      simp only [hlt, ↓reduceIte, spec_ok]
      apply hcont
      simp [hend, Spec.matchBytes]
  · simp

theorem byte_pattern_with_spec (parser : BytePattern) (input : Slice U8)
    (cursor : Cursor) (status : InputStatus) :
    BytePattern.Insts.RusthammerParserInputSharedPatternSliceU8.parse_with parser input cursor (Spec.defaultContext status)
      ⦃ result => Spec.bytePatternOutcome input status parser.pattern cursor result ⦄ := by
  rw [BytePattern.Insts.RusthammerParserInputSharedPatternSliceU8.parse_with_eq]
  step with match_byte_pattern_spec parser.pattern input cursor status as ⟨outcome, houtcome⟩
  cases outcome <;> simp only [spec_ok, Spec.bytePatternOutcome]
  · exact ⟨trivial, houtcome⟩
  · exact houtcome
  · exact houtcome

private theorem primitive_success {α : Type} (status : InputStatus)
    (contract : Spec.ParseResult α → Prop) (next : Cursor) (value : α)
    (h : Partial.primitive status contract (.Success next value)) : contract (.Ok (next, value)) := by
  rcases h with ⟨parsed, hparsed, heq⟩
  cases parsed with
  | Ok pair => cases pair; cases status <;> simp_all [Partial.primitiveResult, Spec.completedResult]
  | Err error => cases status <;> cases error <;> simp_all [Partial.primitiveResult, Spec.completedResult]

theorem byte_success (input : Slice U8) (cursor next : Cursor) (value : U8) (status : InputStatus)
    (h : Partial.primitive status (Spec.byteOutcome input cursor) (.Success next value)) :
    Spec.validCursor input cursor ∧ Spec.validCursor input next ∧
      Spec.position next = Spec.position cursor + 8 ∧
      value.val = Spec.unsignedBits input (Spec.position cursor) 8 := by
  have hraw := primitive_success status _ next value h
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
theorem match_bytes_success (input : Slice U8) (status : InputStatus) (bytes : List U8)
    (cursor next : Cursor) (h : Spec.matchBytes input status bytes cursor (.Success next ())) :
    Spec.position next = Spec.position cursor + 8 * bytes.length ∧
      ∀ i (hi : i < bytes.length),
        bytes[i].val = Spec.unsignedBits input (Spec.position cursor + 8 * i) 8 := by
  induction bytes generalizing cursor with
  | nil =>
    simp only [Spec.matchBytes, ParseOutcome.Success.injEq, and_true] at h
    subst next
    simp
  | cons expected rest ih =>
    rcases h with ⟨decoded, hdecoded, hrest⟩
    cases decoded with
    | NeedMore => cases hrest
    | Error error => cases hrest
    | Success middle value =>
      by_cases heq : value = expected
      · simp only [if_pos heq] at hrest
        have hbyte := byte_success input cursor middle value status hdecoded
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

theorem byte_pattern_success (input : Slice U8) (status : InputStatus) (pattern output : Slice U8)
    (cursor next : Cursor) (h : Spec.bytePatternOutcome input status pattern cursor (.Success next output)) :
    output = pattern ∧ Spec.position next = Spec.position cursor + 8 * pattern.val.length ∧
      ∀ i (hi : i < pattern.val.length),
        pattern.val[i].val = Spec.unsignedBits input (Spec.position cursor + 8 * i) 8 := by
  exact ⟨h.1, match_bytes_success input status pattern.val cursor next h.2⟩

theorem match_bytes_final_not_more (input : Slice U8) (bytes : List U8) (cursor : Cursor) :
    ¬Spec.matchBytes input .Final bytes cursor .NeedMore := by
  intro h
  induction bytes generalizing cursor with
  | nil => cases h
  | cons expected rest ih =>
    rcases h with ⟨decoded, ⟨parsed, _hparsed, rfl⟩, hrest⟩
    cases parsed with
    | Err error => cases hrest
    | Ok pair =>
      rcases pair with ⟨next, value⟩
      simp only [Partial.primitiveResult, Spec.completedResult] at hrest
      split at hrest
      · exact ih next hrest
      · cases hrest

/-- Finality excludes incompleteness for arbitrary patterns, including empty ones. -/
theorem byte_pattern_final_spec (parser : BytePattern) (input : Slice U8) (cursor : Cursor) :
    BytePattern.Insts.RusthammerParserInputSharedPatternSliceU8.parse_with parser input cursor ParseContext.FINAL
      ⦃ result => Spec.completed (Spec.bytePatternComplete input parser.pattern cursor) result ⦄ := by
  simp only [ParseContext.FINAL]
  step with byte_pattern_with_spec parser input cursor .Final as ⟨outcome, houtcome⟩
  cases outcome with
  | Success next output => exact ⟨.Ok (next, output), houtcome, rfl⟩
  | Error error => exact ⟨.Err error, houtcome, rfl⟩
  | NeedMore => exact False.elim (match_bytes_final_not_more input parser.pattern.val cursor houtcome)

theorem byte_pattern_spec (parser : BytePattern) (input : Slice U8) (cursor : Cursor) :
    DirectParser.parse BytePattern.Insts.RusthammerParserInputSharedPatternSliceU8 parser input cursor
      ⦃ result => Spec.bytePatternComplete input parser.pattern cursor result ⦄ := by
  exact complete_spec BytePattern.Insts.RusthammerParserInputSharedPatternSliceU8 parser input cursor
    (Spec.bytePatternComplete input parser.pattern cursor) (byte_pattern_final_spec parser input cursor)

end RustHammer.Proofs
