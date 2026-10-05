import RustHammer.Spec

open Aeneas Aeneas.Std Result WP

namespace RustHammer.Proofs
open Code

@[step]
theorem read_bit_success (input : Slice U8) (cursor : Cursor)
    (hbit : cursor.bit.val < 8) (hbyte : cursor.byte.val < input.val.length) :
    read_bit input cursor ⦃ result => Spec.bitSuccess input cursor result ⦄ := by
  have hbitBound : ¬cursor.bit ≥ 8#u8 := by scalar_tac
  have hbyteBound : ¬cursor.byte ≥ input.len := by scalar_tac
  simp only [read_bit, read_bit_ordered, hbitBound, hbyteBound, ↓reduceIte]
  step as ⟨shift, hshift⟩
  step as ⟨byte, hbyteValue⟩
  step as ⟨shifted, hshifted, hshiftedBv⟩
  step as ⟨masked, hmasked, hmaskedBv⟩
  split
  · step as ⟨next, hnext⟩
    simp only [Spec.bitSuccess]
    refine ⟨_, _, rfl, ?_, ?_, ?_⟩
    · scalar_tac
    · scalar_tac
    · simp_all [Nat.testBit]
      apply Bool.eq_iff_iff.mpr
      simp only [bne_iff_ne, beq_iff_eq]
      scalar_tac
  · step as ⟨next, hnext⟩
    simp only [Spec.bitSuccess]
    refine ⟨_, _, rfl, ?_, ?_, ?_⟩
    · scalar_tac
    · scalar_tac
    · simp_all [Nat.testBit]
      apply Bool.eq_iff_iff.mpr
      simp only [bne_iff_ne, beq_iff_eq]
      scalar_tac

/-- Every position with no readable bit returns the specified parser error. -/
theorem read_bit_failure (input : Slice U8) (cursor : Cursor)
    (hfail : ¬(cursor.bit.val < 8 ∧ cursor.byte.val < input.val.length)) :
    read_bit input cursor ⦃ result => result = .Err
      (if cursor.bit.val < 8 ∧ cursor.byte.val = input.val.length ∧ cursor.bit.val = 0
       then ParseError.UnexpectedEnd else ParseError.InvalidCursor) ⦄ := by
  by_cases hbit : cursor.bit ≥ 8#u8
  · have hbad : ¬cursor.bit.val < 8 := by scalar_tac
    simp [read_bit, read_bit_ordered, hbit, hbad, spec_ok]
  · have hbyte : cursor.byte ≥ input.len := by scalar_tac
    simp only [read_bit, read_bit_ordered, hbit, hbyte, ↓reduceIte]
    by_cases heq : cursor.byte = input.len <;>
      by_cases hzero : cursor.bit = 0#u8 <;>
      simp_all [spec_ok]

/-- An aligned, in-bounds payload is exactly the requested input subsequence. -/
theorem take_aligned_success (input : Slice U8) (cursor : Cursor) (count : Usize)
    (haligned : cursor.bit = 0#u8)
    (hbound : cursor.byte.val + count.val ≤ input.val.length) :
    take_aligned input cursor count
      ⦃ result => Spec.takeAlignedSuccess input cursor count result ⦄ := by
  unfold Spec.takeAlignedSuccess
  have hbyte : ¬cursor.byte > input.len := by scalar_tac
  simp [take_aligned,
    haligned, hbyte]
  step as ⟨remaining, hremaining⟩
  split
  · scalar_tac
  · step as ⟨last, hlast⟩
    step as ⟨payload, hpayload, hlength⟩
    refine ⟨_, _, rfl, hlast, rfl, ?_⟩
    simp_all [List.slice]

/-- Invalid raw cursors are rejected before alignment or length is considered. -/
theorem take_aligned_invalid_cursor (input : Slice U8) (cursor : Cursor) (count : Usize)
    (hinvalid : ¬(cursor.bit.val < 8 ∧ cursor.byte.val ≤ input.val.length ∧
      (cursor.byte.val = input.val.length → cursor.bit.val = 0))) :
    take_aligned input cursor count
      ⦃ result => result = .Err ParseError.InvalidCursor ⦄ := by
  by_cases hbit : cursor.bit ≥ 8#u8
  · simp [take_aligned,
      hbit, spec_ok]
  · by_cases hbyte : cursor.byte > input.len
    · simp [take_aligned,
        hbit, hbyte, spec_ok]
    · have heq : cursor.byte = input.len := by scalar_tac
      have hnonzero : cursor.bit ≠ 0#u8 := by scalar_tac
      simp [take_aligned,
        hbit, heq, hnonzero, spec_ok]

/-- A valid cursor inside a byte is unaligned, even for an empty payload. -/
theorem take_aligned_unaligned (input : Slice U8) (cursor : Cursor) (count : Usize)
    (hbit : 0 < cursor.bit.val ∧ cursor.bit.val < 8)
    (hbyte : cursor.byte.val < input.val.length) :
    take_aligned input cursor count
      ⦃ result => result = .Err ParseError.Unaligned ⦄ := by
  have hbitBound : ¬cursor.bit ≥ 8#u8 := by scalar_tac
  have hbyteBound : ¬cursor.byte > input.len := by scalar_tac
  have hnotend : cursor.byte ≠ input.len := by scalar_tac
  have hnonzero : cursor.bit ≠ 0#u8 := by scalar_tac
  simp [take_aligned,
    hbitBound, hbyteBound, hnotend, hnonzero, spec_ok]

/-- Insufficient input is an ordinary parsing error, including huge lengths. -/
theorem take_aligned_truncated (input : Slice U8) (cursor : Cursor) (count : Usize)
    (haligned : cursor.bit = 0#u8) (hbyte : cursor.byte.val ≤ input.val.length)
    (hshort : input.val.length < cursor.byte.val + count.val) :
    take_aligned input cursor count
      ⦃ result => result = .Err ParseError.UnexpectedEnd ⦄ := by
  have hbyteBound : ¬cursor.byte > input.len := by scalar_tac
  simp [take_aligned,
    haligned, hbyteBound]
  step as ⟨remaining, hremaining⟩
  split
  · simp only [spec_ok]
  · scalar_tac

/-- Borrowed payload parsing terminates normally for every input, cursor, and count. -/
theorem take_aligned_spec (input : Slice U8) (cursor : Cursor) (count : Usize) :
    take_aligned input cursor count
      ⦃ result => Spec.takeAlignedOutcome input cursor count result ⦄ := by
  unfold Spec.takeAlignedOutcome
  by_cases hvalid : cursor.bit.val < 8 ∧ cursor.byte.val ≤ input.val.length ∧
      (cursor.byte.val = input.val.length → cursor.bit.val = 0)
  · simp only [if_pos hvalid]
    by_cases haligned : cursor.bit.val = 0
    · have hzero : cursor.bit = 0#u8 := by scalar_tac
      simp only [haligned, ↓reduceIte]
      by_cases hbound : cursor.byte.val + count.val ≤ input.val.length
      · simp only [hbound, ↓reduceIte]
        exact take_aligned_success input cursor count hzero hbound
      · simp only [hbound, ↓reduceIte]
        exact take_aligned_truncated input cursor count hzero hvalid.2.1 (by omega)
    · simp only [haligned, ↓reduceIte]
      exact take_aligned_unaligned input cursor count (by omega) (by omega)
  · simp only [if_neg hvalid]
    exact take_aligned_invalid_cursor input cursor count hvalid

end RustHammer.Proofs
