import RustHammer.PositionSpec
import RustHammer.ParserProofs

open RustHammer.Code.grammar.position
  RustHammer.Code.input_types

open Aeneas Aeneas.Std Result WP

namespace RustHammer.Proofs
open Code

/-- Total cursor advancement for every machine-representable length, raw cursor,
and count. Every addition, subtraction, division, and cast is proved safe. -/
theorem advance_cursor_spec (length : Usize) (cursor : Cursor) (bits : Usize) :
    advance_cursor length cursor bits
      ⦃ result => Spec.advanceOutcome length.val cursor bits.val result ⦄ := by
  unfold Spec.advanceOutcome advance_cursor
  by_cases hvalid : Spec.validPosition length.val cursor
  · have hparts := hvalid
    unfold Spec.validPosition Spec.position at hparts
    have hbit : ¬cursor.bit ≥ 8#u8 := by scalar_tac
    have hbyte : ¬cursor.byte > length := by scalar_tac
    simp only [if_pos hvalid, hbit, hbyte, ↓reduceIte]
    split <;> (try (
      have hzero : cursor.bit = 0#u8 := by scalar_tac
      simp only [hzero, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    ))
    all_goals
      step as ⟨remainder, hremainder⟩
      step with UScalar.cast_inBounds_spec .U8 remainder (by scalar_tac) as ⟨small, hsmall⟩
      step as ⟨tail, htail⟩
      step as ⟨whole, hwhole⟩
      step as ⟨carry, hcarry⟩
      step with UScalar.cast_inBounds_spec .Usize carry (by scalar_tac) as ⟨wide, hwide⟩
      step as ⟨bytes, hbytes⟩
      step as ⟨bit, hbitval⟩
      step as ⟨remaining, hremaining⟩
      by_cases hshort : bytes > remaining
      · have hn : ¬Spec.position cursor + bits.val ≤ 8 * length.val := by
          unfold Spec.position
          scalar_tac
        simp [hshort, hn, spec_ok]
      · simp only [hshort, ↓reduceIte]
        step as ⟨byte, hbyteval⟩
        have hposition : Spec.position { byte, bit } = Spec.position cursor + bits.val := by
          unfold Spec.position
          scalar_tac
        have hbytele : byte.val ≤ length.val := by scalar_tac
        have hbitlt : bit.val < 8 := by omega
        by_cases hend : byte = length
        · have hbyteeq : byte.val = length.val := congrArg (fun x : Usize => x.val) hend
          by_cases hnonzero : bit ≠ 0#u8
          · have hbitne : bit.val ≠ 0 := fun h => hnonzero (UScalar.eq_of_val_eq h)
            have hn : ¬Spec.position cursor + bits.val ≤ 8 * length.val := by
              change 8 * byte.val + bit.val = Spec.position cursor + bits.val at hposition
              omega
            simp [hend, hnonzero, hn, spec_ok]
          · have hbitzero : bit.val = 0 :=
              congrArg (fun x : U8 => x.val) (Classical.not_not.mp hnonzero)
            have hfit : Spec.position cursor + bits.val ≤ 8 * length.val := by
              change 8 * byte.val + bit.val = Spec.position cursor + bits.val at hposition
              omega
            simp only [hend, bne_iff_ne, hnonzero, ↓reduceIte, if_pos hfit, spec_ok]
            refine ⟨{ byte, bit }, ?_, hbitlt, ?_, hposition⟩
            · simp only [hend]
            · rw [hposition]; exact hfit
        · have hbytene : byte.val ≠ length.val := fun h => hend (UScalar.eq_of_val_eq h)
          have hfit : Spec.position cursor + bits.val ≤ 8 * length.val := by
            change 8 * byte.val + bit.val = Spec.position cursor + bits.val at hposition
            omega
          simp only [hend, ↓reduceIte, if_pos hfit, spec_ok]
          refine ⟨{ byte, bit }, rfl, hbitlt, ?_, hposition⟩
          rw [hposition]; exact hfit
  · simp only [if_neg hvalid]
    have hparts := hvalid
    unfold Spec.validPosition Spec.position at hparts
    by_cases hbit : cursor.bit ≥ 8#u8
    · simp [hbit, spec_ok]
    · by_cases hbyte : cursor.byte > length
      · simp [hbit, hbyte, spec_ok]
      · have heq : cursor.byte = length := by scalar_tac
        have hnonzero : cursor.bit ≠ 0#u8 := by scalar_tac
        simp [hbit, heq, hnonzero, spec_ok]

theorem skip_bits_new_spec (bits : Usize) :
    SkipBits.new bits ⦃ parser => parser.bits = bits ⦄ := by
  simp [SkipBits.new, spec_ok]

theorem skip_bits_bits_spec (parser : SkipBits) :
    SkipBits.impl.bits parser ⦃ bits => bits = parser.bits ⦄ := by
  simp [SkipBits.impl.bits, spec_ok]

theorem skip_bits_clone_spec (parser : SkipBits) :
    SkipBits.Insts.CoreCloneClone.clone parser ⦃ copied => copied = parser ⦄ := by
  simp [SkipBits.Insts.CoreCloneClone.clone, spec_ok]

theorem tell_clone_spec (parser : Tell) :
    Tell.Insts.CoreCloneClone.clone parser ⦃ copied => copied = parser ⦄ := by
  simp [Tell.Insts.CoreCloneClone.clone, spec_ok]

theorem skip_bits_with_spec (parser : SkipBits) (input : Slice U8)
    (cursor : Cursor) :
    SkipBits.Insts.RusthammerParser_traitsParserInputTuple.parse_with parser input cursor ByteOrder.Big
      ⦃ result => Spec.skipBitsOutcome input cursor parser.bits result ⦄ := by
  rw [SkipBits.Insts.RusthammerParser_traitsParserInputTuple.parse_with]
  step with advance_cursor_spec input.len cursor parser.bits as ⟨advanced, hadvanced⟩
  cases advanced with
  | Ok next =>
    simp only [spec_ok]
    exact ⟨.Ok next, hadvanced, rfl⟩
  | Err error =>
    simp only [spec_ok]
    exact ⟨.Err error, hadvanced, rfl⟩

theorem skip_bits_spec (parser : SkipBits) (input : Slice U8) (cursor : Cursor) :
    parser_traits.Parser.parse.default SkipBits.Insts.RusthammerParser_traitsParserInputTuple parser input cursor
      ⦃ result => Spec.skipBitsOutcome input cursor parser.bits result ⦄ := by
  apply complete_spec
  simpa only [SkipBits.Insts.RusthammerParser_traitsParserInputTuple.parse_with, ByteOrder.Big] using
    skip_bits_with_spec parser input cursor

private theorem normalized_position_injective (first second : Cursor)
    (hf : first.bit.val < 8) (hs : second.bit.val < 8)
    (heq : Spec.position first = Spec.position second) : first = second := by
  unfold Spec.position at heq
  have hb : first.byte = second.byte := by scalar_tac
  have ht : first.bit = second.bit := by scalar_tac
  cases first
  cases second
  simp_all

/-- A zero count validates the cursor and then preserves it, even at the end. -/
theorem advance_cursor_zero_spec (length : Usize) (cursor : Cursor) :
    advance_cursor length cursor 0#usize
      ⦃ result => result = if Spec.validPosition length.val cursor then .Ok cursor else .Err .InvalidCursor ⦄ := by
  step with advance_cursor_spec length cursor 0#usize as ⟨result, hresult⟩
  by_cases hv : Spec.validPosition length.val cursor
  · simp only [Spec.advanceOutcome, if_pos hv, Nat.add_zero,
      if_pos hv.2] at hresult
    rcases hresult with ⟨next, rfl, hnext, hpos⟩
    have heq := normalized_position_injective next cursor hnext.1 hv.1 (by simpa using hpos)
    simp [hv, heq]
  · simpa only [Spec.advanceOutcome, if_neg hv] using hresult

theorem tell_with_spec (input : Slice U8) (cursor : Cursor) :
    Tell.Insts.RusthammerParser_traitsParserInputCursor.parse_with () input cursor ByteOrder.Big
      ⦃ result => Spec.tellOutcome input cursor result ⦄ := by
  rw [Tell.Insts.RusthammerParser_traitsParserInputCursor.parse_with]
  step with advance_cursor_zero_spec input.len cursor as ⟨advanced, hadvanced⟩
  by_cases hv : Spec.validCursor input cursor
  · have heq : advanced = .Ok cursor := by
      simpa only [Spec.validPosition, Slice.len_val, if_pos hv] using hadvanced
    simp only [heq, spec_ok]
    simp only [Spec.tellOutcome, if_pos hv]
  · have heq : advanced = .Err .InvalidCursor := by
      simpa only [Spec.validPosition, Slice.len_val, if_neg hv] using hadvanced
    simp only [heq, spec_ok]
    simp only [Spec.tellOutcome, if_neg hv]

theorem tell_spec (input : Slice U8) (cursor : Cursor) :
    parser_traits.Parser.parse.default Tell.Insts.RusthammerParser_traitsParserInputCursor () input cursor
      ⦃ result => Spec.tellOutcome input cursor result ⦄ := by
  exact complete_spec Tell.Insts.RusthammerParser_traitsParserInputCursor () input cursor _
    (tell_with_spec input cursor)

theorem skip_bits_final_spec (parser : SkipBits) (input : Slice U8) (cursor : Cursor) :
    SkipBits.Insts.RusthammerParser_traitsParserInputTuple.parse_with parser input cursor ByteOrder.Big
      ⦃ result => Spec.skipBitsOutcome input cursor parser.bits result ⦄ := by
  simpa only [SkipBits.Insts.RusthammerParser_traitsParserInputTuple.parse_with, ByteOrder.Big] using
    skip_bits_with_spec parser input cursor

theorem skip_bits_zero_with_spec (input : Slice U8) (cursor : Cursor) :
    SkipBits.Insts.RusthammerParser_traitsParserInputTuple.parse_with { bits := 0#usize } input cursor ByteOrder.Big
      ⦃ result => result = if Spec.validCursor input cursor then .Ok (cursor, ()) else .Err .InvalidCursor ⦄ := by
  rw [SkipBits.Insts.RusthammerParser_traitsParserInputTuple.parse_with]
  step with advance_cursor_zero_spec input.len cursor as ⟨advanced, hadvanced⟩
  by_cases hv : Spec.validCursor input cursor
  · have heq : advanced = .Ok cursor := by
      simpa only [Spec.validPosition, Slice.len_val, if_pos hv] using hadvanced
    simp [heq, hv, spec_ok]
  · have heq : advanced = .Err .InvalidCursor := by
      simpa only [Spec.validPosition, Slice.len_val, if_neg hv] using hadvanced
    simp [heq, hv, spec_ok]

theorem skip_bits_success (input : Slice U8) (cursor next : Cursor) (bits : Usize)
    (h : (Spec.skipBitsOutcome input cursor bits) (.Ok (next, ()))) :
    Spec.validCursor input cursor ∧ Spec.validCursor input next ∧
      Spec.position next = Spec.position cursor + bits.val := by
  rcases h with ⟨advanced, hadvanced, heq⟩
  cases advanced with
  | Err error => cases error <;> cases heq
  | Ok after =>
    have hn : next = after := by
      simpa [] using heq
    subst after
    unfold Spec.advanceOutcome at hadvanced
    split at hadvanced
    · rename_i hv
      split at hadvanced
      · rcases hadvanced with ⟨last, heq, hlast, hpos⟩
        cases heq
        exact ⟨hv, hlast, hpos⟩
      · cases hadvanced
    · cases hadvanced

end RustHammer.Proofs

namespace RustHammer.Ordering
open Code Proofs

theorem skip_bits_with_spec (parser : SkipBits) (input : Slice U8) (cursor : Cursor)
    (context : ByteOrder) :
    SkipBits.Insts.RusthammerParser_traitsParserInputTuple.parse_with parser input cursor context
      ⦃ result => Spec.skipBitsOutcome input cursor parser.bits result ⦄ := by
  exact Proofs.skip_bits_with_spec parser input cursor

theorem tell_with_spec (input : Slice U8) (cursor : Cursor) (context : ByteOrder) :
    Tell.Insts.RusthammerParser_traitsParserInputCursor.parse_with () input cursor context
      ⦃ result => Spec.tellOutcome input cursor result ⦄ := by
  exact Proofs.tell_with_spec input cursor

end RustHammer.Ordering
