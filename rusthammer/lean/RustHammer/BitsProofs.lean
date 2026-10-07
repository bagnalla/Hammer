import RustHammer.Proofs
import RustHammer.BitsSpec

open RustHammer.Code.grammar.numeric
  RustHammer.Code.input_types

open Aeneas Aeneas.Std Result WP

namespace RustHammer.Proofs
open Code

/-- Construction is total and rejects exactly the unsupported widths. -/
theorem bits_new_spec (width : U8) :
    Bits.new width ⦃ result => Spec.bitsNewOutcome width result ⦄ := by
  by_cases hwidth : width.val ≤ 64
  · have hbound : ¬width > 64#u8 := by scalar_tac
    simp [Bits.new, Spec.bitsNewOutcome, hwidth, hbound, spec_ok]
  · have hbound : width > 64#u8 := by scalar_tac
    simp [Bits.new, Spec.bitsNewOutcome, hwidth, hbound, spec_ok]

/-- Every successful constructor call establishes the parser's invariant. -/
theorem bits_new_valid (width : U8) (parser : Bits)
    (hnew : Bits.new width = ok (.Ok parser)) : Spec.validBits parser := by
  have hspec := bits_new_spec width
  rw [hnew] at hspec
  simp only [spec_ok, Spec.bitsNewOutcome] at hspec
  split at hspec
  · cases hspec
    assumption
  · cases hspec

theorem bits_width_spec (parser : Bits) :
    Bits.impl.width parser ⦃ result => result = parser.width ⦄ := by
  simp [Bits.impl.width, spec_ok]

theorem bitAt_le_one (input : Slice U8) (pos : Nat) : Spec.bitAt input pos ≤ 1 := by
  unfold Spec.bitAt
  split <;> omega

theorem unsignedBits_lt_pow (input : Slice U8) (start width : Nat) :
    Spec.unsignedBits input start width < 2 ^ width := by
  induction width generalizing start with
  | zero => simp [Spec.unsignedBits]
  | succ width ih =>
    have htail := ih (start + 1)
    have hdigit := bitAt_le_one input start
    simp only [Spec.unsignedBits, Nat.pow_succ]
    nlinarith

/-- The existing bit-reader contract yields absolute-position facts for numeric fields. -/
theorem bit_success_position (input : Slice U8) (cursor next : Cursor) (value : Bool)
    (hbit : cursor.bit.val < 8) (hbyte : cursor.byte.val < input.val.length)
    (hsuccess : Spec.bitSuccess input cursor (.Ok (next, value))) :
    Spec.validCursor input next ∧ Spec.position next = Spec.position cursor + 1 ∧
      (if value then 1 else 0) = Spec.bitAt input (Spec.position cursor) := by
  rcases hsuccess with ⟨last, digit, heq, hnextByte, hnextBit, hvalue⟩
  cases heq
  have hdiv : Spec.position cursor / 8 = cursor.byte.val := by
    unfold Spec.position
    omega
  have hmod : Spec.position cursor % 8 = cursor.bit.val := by
    unfold Spec.position
    omega
  constructor
  · unfold Spec.validCursor Spec.position
    split_ifs at hnextByte <;> omega
  constructor
  · unfold Spec.position
    split_ifs at hnextByte <;> omega
  · simp only [Spec.bitAt, hdiv, hmod, hvalue]

/-- Appending one binary digit stays within the accumulator's remaining capacity. -/
theorem append_bit_bound (remaining value digit : Nat)
    (hremaining : 0 < remaining ∧ remaining ≤ 64)
    (hvalue : value < 2 ^ (64 - remaining)) (hdigit : digit ≤ 1) :
    value * 2 + digit < 2 ^ (64 - (remaining - 1)) ∧
      value * 2 + digit < 2 ^ 64 := by
  have hexp : 64 - (remaining - 1) = (64 - remaining) + 1 := by omega
  have hnext : value * 2 + digit < 2 ^ (64 - (remaining - 1)) := by
    rw [hexp, Nat.pow_succ]
    omega
  refine ⟨hnext, lt_of_lt_of_le hnext ?_⟩
  exact Nat.pow_le_pow_right (by omega) (by omega)

/-- The loop maintains a positional-value invariant and decreases the remaining width. -/
theorem bits_loop_spec (input : Slice U8) (cursor : Cursor) (width : U8)
    (hwidth : width.val ≤ 64) (hvalid : Spec.validCursor input cursor) :
    read_bits_loop0 input cursor width 0#u64
      ⦃ result => if Spec.position cursor + width.val ≤ 8 * input.val.length then
          Spec.bitsSuccess input cursor width result
        else result = .Err ParseError.UnexpectedEnd ⦄ := by
  unfold read_bits_loop0
  apply loop.spec_decr_nat (fun state => state.2.1.val)
    (fun (next, remaining, value) =>
      Spec.validCursor input next ∧ remaining.val ≤ 64 ∧
      value.val < 2 ^ (64 - remaining.val) ∧
      Spec.position next + remaining.val = Spec.position cursor + width.val ∧
      value.val * 2 ^ remaining.val + Spec.unsignedBits input (Spec.position next) remaining.val =
        Spec.unsignedBits input (Spec.position cursor) width.val)
  · rintro ⟨next, remaining, value⟩ ⟨hcur, hrem, hacc, hpos, hdecode⟩
    unfold read_bits_loop0.body
    by_cases hzero : remaining = 0#u8
    · have hzeroNat : remaining.val = 0 := by scalar_tac
      have hfit : Spec.position cursor + width.val ≤ 8 * input.val.length := by
        simp only [Spec.validCursor] at hcur
        omega
      simp only [hzero]
      simp only [hfit, ↓reduceIte, Spec.bitsSuccess]
      refine ⟨next, value, rfl, hcur, ?_, ?_⟩
      · omega
      · simpa [hzeroNat, Spec.unsignedBits] using hdecode
    · have hpositive : 0 < remaining.val := by scalar_tac
      simp only [hzero, bne_iff_ne, ne_eq, not_false_eq_true, ↓reduceIte]
      by_cases hreadable : next.byte.val < input.val.length
      · step with read_bit_success input next hcur.1 hreadable as ⟨result, hresult⟩
        rcases hresult with ⟨after, bit, rfl, hbyte, hbit, hval⟩
        have hstep := bit_success_position input next after bit hcur.1 hreadable
          ⟨after, bit, rfl, hbyte, hbit, hval⟩
        have hdigit : (if bit then 1 else 0 : Nat) ≤ 1 := by split <;> omega
        have hbound := append_bit_bound remaining.val value.val (if bit then 1 else 0)
          ⟨hpositive, hrem⟩ hacc hdigit
        step as ⟨twice, htwice⟩
        have hdigitSpec : (if bit then ok 1#u64 else ok 0#u64)
            ⦃ digit => digit.val = (if bit then 1 else 0 : Nat) ⦄ := by
          cases bit <;> simp [spec_ok]
        step with hdigitSpec as ⟨digit, hdigitValue⟩
        step as ⟨acc, haccNext⟩
        step as ⟨rest, hrest⟩
        refine ⟨hstep.1.1, hstep.1.2, by omega, ?_, by omega, ?_, by omega⟩
        · simpa [haccNext, htwice, hdigitValue, hrest] using hbound.1
        · have hremEq : remaining.val = rest.val + 1 := by omega
          rw [hremEq, Spec.unsignedBits, Nat.pow_succ] at hdecode
          rw [haccNext, htwice, hdigitValue, hstep.2.1, hstep.2.2]
          nlinarith
      · have hend : next.byte.val = input.val.length ∧ next.bit.val = 0 := by
          unfold Spec.validCursor Spec.position at hcur
          omega
        step with read_bit_failure input next (by omega) as ⟨result, hresult⟩
        have hshort : ¬Spec.position cursor + width.val ≤ 8 * input.val.length := by
          unfold Spec.position at hpos ⊢
          omega
        simp only [hend.1, hend.2, and_self] at hresult
        simp [hresult, hshort, spec_ok]
  · refine ⟨hvalid, hwidth, ?_, by omega, ?_⟩
    · simp
    · simp

/-- Validated numeric fields satisfy their complete contract for every raw cursor. -/
theorem bits_decode_spec (parser : Bits) (input : Slice U8) (cursor : Cursor)
    (hconfig : Spec.validBits parser) :
    read_bits input cursor parser
      ⦃ result => Spec.bitsOutcome input cursor parser.width result ⦄ := by
  simp only [Spec.bitsOutcome, read_bits]
  by_cases hvalid : Spec.validCursor input cursor
  · have hparts := hvalid
    unfold Spec.validCursor Spec.position at hparts
    have hbit : ¬cursor.bit ≥ 8#u8 := by scalar_tac
    have hbyte : ¬cursor.byte > input.len := by scalar_tac
    simp only [if_pos hvalid, hbit, hbyte, ↓reduceIte]
    split
    · have hzero : cursor.bit = 0#u8 := by scalar_tac
      simp only [hzero]
      exact bits_loop_spec input cursor parser.width hconfig hvalid
    · exact bits_loop_spec input cursor parser.width hconfig hvalid
  · simp only [if_neg hvalid]
    have hparts := hvalid
    unfold Spec.validCursor Spec.position at hparts
    by_cases hbit : cursor.bit ≥ 8#u8
    · simp [hbit, spec_ok]
    · by_cases hbyte : cursor.byte > input.len
      · simp [hbit, hbyte, spec_ok]
      · have heq : cursor.byte = input.len := by scalar_tac
        have hnonzero : cursor.bit ≠ 0#u8 := by scalar_tac
        simp [hbit, heq, hnonzero, spec_ok]

/-- The convenience function has the same total contract as its parser. -/
theorem read_bits_spec (input : Slice U8) (cursor : Cursor) (parser : Bits)
    (hconfig : Spec.validBits parser) :
    read_bits input cursor parser
      ⦃ result => Spec.bitsOutcome input cursor parser.width result ⦄ := by
  exact bits_decode_spec parser input cursor hconfig

/-- Every valid, sufficiently long field returns the specified value and consumption. -/
theorem read_bits_success (input : Slice U8) (cursor : Cursor) (parser : Bits)
    (hconfig : Spec.validBits parser) (hvalid : Spec.validCursor input cursor)
    (hfit : Spec.position cursor + parser.width.val ≤ 8 * input.val.length) :
    read_bits input cursor parser
      ⦃ result => Spec.bitsSuccess input cursor parser.width result ⦄ := by
  simpa only [Spec.bitsOutcome, if_pos hvalid, if_pos hfit]
    using read_bits_spec input cursor parser hconfig

end RustHammer.Proofs
