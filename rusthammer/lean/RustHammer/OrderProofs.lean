import RustHammer.OrderMath

open RustHammer.Code.grammar.numeric
  RustHammer.Code.input_types

open Aeneas Aeneas.Std Result WP

namespace RustHammer.Proofs
open Code

theorem fragment_offset_spec (bit take : U8) (order : BitOrder)
    (hb : bit.val < 8) (ht : 0 < take.val ∧ take.val ≤ 8 - bit.val) :
    fragment_offset bit take order ⦃ offset =>
      offset.val = (match order with | .HighFirst => bit.val | .LowFirst => 8 - bit.val - take.val) ∧
      offset.val < 8 ∧ offset.val + take.val ≤ 8 ⦄ := by
  cases order with
  | HighFirst => simp only [fragment_offset, spec_ok]; exact ⟨trivial, hb, by omega⟩
  | LowFirst =>
    unfold fragment_offset
    step as ⟨available, ha⟩
    step as ⟨offset, ho⟩
    exact ⟨by omega, by omega, by omega⟩

theorem advance_fragment_spec (input : Slice U8) (cursor : Cursor) (take : U8)
    (hb : cursor.bit.val < 8) (hi : cursor.byte.val < input.val.length)
    (ht : 0 < take.val ∧ take.val ≤ 8 - cursor.bit.val) :
    advance_fragment cursor take ⦃ next => Spec.validCursor input next ∧
      Spec.position next = Spec.position cursor + take.val ⦄ := by
  unfold advance_fragment
  step as ⟨bit, hbit⟩
  split
  · step as ⟨byte, hbyte⟩
    simp only [Spec.position]
    scalar_tac
  · simp only [spec_ok, Spec.position]
    scalar_tac

theorem append_fragment_spec (value fragment : U64) (done take : U8) (order : ByteOrder)
    (ht : 0 < take.val ∧ take.val ≤ 8) (htotal : done.val + take.val ≤ 64)
    (hv : value.val < 2 ^ done.val) (hf : fragment.val < 2 ^ take.val) :
    append_fragment value fragment done take order ⦃ result =>
      result.val = (match order with
        | .Big => value.val * 2 ^ take.val + fragment.val
        | .Little => value.val + fragment.val * 2 ^ done.val) ∧
      result.val < 2 ^ (done.val + take.val) ⦄ := by
  have hdone : done.val < 64 := by omega
  have hcapacity : 2 ^ (done.val + take.val) ≤ 2 ^ 64 :=
    Nat.pow_le_pow_right (by omega) htotal
  cases order with
  | Big =>
    have hbound : value.val * 2 ^ take.val + fragment.val < 2 ^ (done.val + take.val) := by
      rw [Nat.pow_add]; nlinarith
    have hmachine : value.val * 2 ^ take.val + fragment.val < 2 ^ 64 := lt_of_lt_of_le hbound hcapacity
    unfold append_fragment
    step as ⟨power, hp, _⟩
    have hpow : 2 ^ take.val < U64.size := by
      simp only [U64.size, U64.numBits]
      exact Nat.pow_lt_pow_right (by decide) (show take.val < 64 by omega)
    have hpv : power.val = 2 ^ take.val := by
      simpa [Nat.one_shiftLeft, Nat.mod_eq_of_lt hpow] using hp
    step as ⟨product, hproduct⟩
    rw [hpv] at hproduct
    step as ⟨result, hresult⟩
    exact ⟨by omega, by omega⟩
  | Little =>
    have hbound : value.val + fragment.val * 2 ^ done.val < 2 ^ (done.val + take.val) := by
      rw [Nat.pow_add]; nlinarith
    have hmachine : value.val + fragment.val * 2 ^ done.val < 2 ^ 64 := lt_of_lt_of_le hbound hcapacity
    unfold append_fragment
    step as ⟨power, hp, _⟩
    have hpow : 2 ^ done.val < U64.size := by
      simp only [U64.size, U64.numBits]
      exact Nat.pow_lt_pow_right (by omega) hdone
    have hpv : power.val = 2 ^ done.val := by
      simpa [Nat.one_shiftLeft, Nat.mod_eq_of_lt hpow] using hp
    step as ⟨product, hproduct⟩
    rw [hpv] at hproduct
    step as ⟨result, hresult⟩
    exact ⟨by omega, by omega⟩

/-- The accumulator is bounded by consumed width. The remaining mathematical
field, weighted according to byte order, completes the specified original value. -/
theorem fragments_loop_spec (input : Slice U8) (cursor : Cursor) (width : U8) (order : Order)
    (hw : width.val ≤ 64) (hc : Spec.validCursor input cursor) :
    read_fragments_loop0 input width order cursor width 0#u64
      ⦃ result => if Spec.position cursor + width.val ≤ 8 * input.val.length then
          Ordering.success input cursor width order result
        else result = .Err .UnexpectedEnd ⦄ := by
  unfold read_fragments_loop0
  apply loop.spec_decr_nat (fun state => state.2.1.val)
    (fun (next, remaining, value) =>
      Spec.validCursor input next ∧ remaining.val ≤ width.val ∧
      value.val < 2 ^ (width.val - remaining.val) ∧
      Spec.position next + remaining.val = Spec.position cursor + width.val ∧
      (match order.byte with
      | .Big => value.val * 2 ^ remaining.val +
          Ordering.unsigned input order (Spec.position next) remaining.val
      | .Little => value.val + 2 ^ (width.val - remaining.val) *
          Ordering.unsigned input order (Spec.position next) remaining.val) =
        Ordering.unsigned input order (Spec.position cursor) width.val)
  · rintro ⟨next, remaining, value⟩ ⟨hcur, hrem, hacc, hpos, hdecode⟩
    unfold read_fragments_loop0.body
    by_cases hz : remaining = 0#u8
    · have hzn : remaining.val = 0 := by scalar_tac
      have hfit : Spec.position cursor + width.val ≤ 8 * input.val.length := by
        unfold Spec.validCursor at hcur
        omega
      simp only [hz, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, if_pos hfit, Ordering.success]
      refine ⟨next, value, rfl, hcur, by omega, ?_⟩
      cases ho : order.byte <;> simpa [hzn, ho] using hdecode
    · have hrpos : 0 < remaining.val := by scalar_tac
      simp only [bne_iff_ne, hz, ne_eq, not_false_eq_true, ↓reduceIte]
      by_cases he : next.byte = input.len
      · have hshort : ¬Spec.position cursor + width.val ≤ 8 * input.val.length := by
          simp only [Spec.validCursor, Spec.position] at hcur hpos ⊢
          scalar_tac
        simp [he, hshort, spec_ok]
      · have hi : next.byte.val < input.val.length := by
          unfold Spec.validCursor Spec.position at hcur
          scalar_tac
        simp only [he, ↓reduceIte]
        step as ⟨available, havail⟩
        have htakeSpec : (if remaining < available then ok remaining else ok available)
            ⦃ take => take.val = min remaining.val (8 - next.bit.val) ⦄ := by
          split <;> simp only [spec_ok] <;> scalar_tac
        step with htakeSpec as ⟨take, htake⟩
        have ht : 0 < take.val ∧ take.val ≤ remaining.val ∧ take.val ≤ 8 - next.bit.val := by
          have hb := hcur.1
          omega
        step with fragment_offset_spec next.bit take order.bit hcur.1 ⟨ht.1, ht.2.2⟩
          as ⟨offset, hoff, hoffb, hofft⟩
        have hphysical : Spec.validCursor input { next with bit := offset } := by
          change offset.val < 8 ∧ 8 * next.byte.val + offset.val ≤ 8 * input.val.length
          omega
        have hphysicalFit : Spec.position { next with bit := offset } + take.val ≤ 8 * input.val.length := by
          change 8 * next.byte.val + offset.val + take.val ≤ 8 * input.val.length
          omega
        step with read_bits_success input { next with bit := offset } { width := take }
          (by change take.val ≤ 64; omega) hphysical hphysicalFit as ⟨parsed, hparsed⟩
        rcases hparsed with ⟨physicalEnd, fragment, rfl, _, _, hfragment⟩
        have hf : fragment.val < 2 ^ take.val := by
          rw [hfragment]
          exact unsignedBits_lt_pow _ _ _
        step as ⟨done, hdone⟩
        step with append_fragment_spec value fragment done take order.byte
          ⟨ht.1, by omega⟩ (by omega) (by simpa [hdone] using hacc) hf
          as ⟨acc, happend, haccbound⟩
        step with advance_fragment_spec input next take hcur.1 hi ⟨ht.1, ht.2.2⟩
          as ⟨after, hafterBit, hafterBound, hafterpos⟩
        step as ⟨rest, hrest⟩
        have hdoneNext : width.val - rest.val = done.val + take.val := by omega
        have htWidth : Ordering.fragmentWidth (Spec.position next) remaining.val = take.val := by
          unfold Ordering.fragmentWidth Spec.position
          have hb := hcur.1
          omega
        have hfragmentStart : Ordering.fragmentStart order.bit (Spec.position next) take.val =
            Spec.position { next with bit := offset } := by
          unfold Ordering.fragmentStart Spec.position
          have hb := hcur.1
          have hdiv : (8 * next.byte.val + next.bit.val) / 8 = next.byte.val := by omega
          have hmod : (8 * next.byte.val + next.bit.val) % 8 = next.bit.val := by omega
          rw [hdiv, hmod, hoff]
          rfl
        have hunsigned : Ordering.unsigned input order (Spec.position next) remaining.val =
            match order.byte with
            | .Big => fragment.val * 2 ^ rest.val + Ordering.unsigned input order (Spec.position after) rest.val
            | .Little => fragment.val + 2 ^ take.val * Ordering.unsigned input order (Spec.position after) rest.val := by
          rw [Ordering.unsigned, if_neg (by omega)]
          dsimp only
          rw [htWidth, hfragmentStart,
            ← hfragment, ← hrest, ← hafterpos]
          rfl
        refine ⟨hafterBit, hafterBound, by omega, ?_, by omega, ?_, by omega⟩
        · simpa only [hdoneNext] using haccbound
        · have hremaining : remaining.val = take.val + rest.val := by omega
          rw [hunsigned] at hdecode
          cases ho : order.byte <;> simp only [ho] at hdecode happend ⊢
          · rw [happend]
            rw [hremaining, Nat.pow_add] at hdecode
            nlinarith only [hdecode]
          · rw [happend, hdoneNext, Nat.pow_add]
            rw [hdone] at *
            nlinarith only [hdecode]
  · refine ⟨hc, by omega, by simp, by omega, ?_⟩
    cases order.byte <;> simp

theorem read_fragments_spec (input : Slice U8) (cursor : Cursor) (width : U8) (order : Order)
    (hw : width.val ≤ 64) :
    read_fragments input cursor width order
      ⦃ result => Ordering.outcome input cursor width order result ⦄ := by
  simp only [Ordering.outcome, read_fragments]
  by_cases hvalid : Spec.validCursor input cursor
  · have hparts := hvalid
    unfold Spec.validCursor Spec.position at hparts
    have hbit : ¬cursor.bit ≥ 8#u8 := by scalar_tac
    have hbyte : ¬cursor.byte > input.len := by scalar_tac
    simp only [if_pos hvalid, hbit, hbyte, ↓reduceIte]
    split
    · have hzero : cursor.bit = 0#u8 := by scalar_tac
      simp only [hzero]
      exact fragments_loop_spec input cursor width order hw hvalid
    · exact fragments_loop_spec input cursor width order hw hvalid
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

theorem read_ordered_bits_spec (input : Slice U8) (cursor : Cursor) (parser : Bits) (order : Order)
    (hw : Spec.validBits parser) :
    read_ordered_bits input cursor parser order
      ⦃ result => Ordering.outcome input cursor parser.width order result ⦄ := by
  rcases order with ⟨bit, byte⟩
  cases bit <;> cases byte <;> simp only [read_ordered_bits]
  · have h := read_bits_spec input cursor parser hw
    simpa only [← Ordering.outcome_default, Order.DEFAULT] using h
  all_goals exact read_fragments_spec input cursor parser.width _ hw

theorem read_bit_ordered_success (input : Slice U8) (cursor : Cursor) (order : BitOrder)
    (hb : cursor.bit.val < 8) (hi : cursor.byte.val < input.val.length) :
    read_bit_ordered input cursor order
      ⦃ result => Ordering.bitSuccess input cursor order result ⦄ := by
  cases order with
  | HighFirst =>
    simpa only [read_bit, Ordering.bitSuccess, Spec.bitSuccess] using
      read_bit_success input cursor hb hi
  | LowFirst =>
    have hbitBound : ¬cursor.bit ≥ 8#u8 := by scalar_tac
    have hbyteBound : ¬cursor.byte ≥ input.len := by scalar_tac
    simp only [read_bit_ordered, hbitBound, hbyteBound, ↓reduceIte]
    step as ⟨byte, hbyteValue⟩
    step as ⟨shifted, hshifted, hshiftedBv⟩
    step as ⟨masked, hmasked, hmaskedBv⟩
    split
    · step as ⟨next, hnext⟩
      simp only [Ordering.bitSuccess]
      refine ⟨_, _, rfl, ?_, ?_, ?_⟩
      · scalar_tac
      · scalar_tac
      · simp_all [Nat.testBit]
        apply Bool.eq_iff_iff.mpr
        simp only [bne_iff_ne, beq_iff_eq]
        scalar_tac
    · step as ⟨next, hnext⟩
      simp only [Ordering.bitSuccess]
      refine ⟨_, _, rfl, ?_, ?_, ?_⟩
      · scalar_tac
      · scalar_tac
      · simp_all [Nat.testBit]
        apply Bool.eq_iff_iff.mpr
        simp only [bne_iff_ne, beq_iff_eq]
        scalar_tac

theorem read_bit_ordered_spec (input : Slice U8) (cursor : Cursor) (order : BitOrder) :
    read_bit_ordered input cursor order
      ⦃ result => Ordering.bitOutcome input cursor order result ⦄ := by
  unfold Ordering.bitOutcome
  by_cases h : cursor.bit.val < 8 ∧ cursor.byte.val < input.val.length
  · simpa only [if_pos h] using read_bit_ordered_success input cursor order h.1 h.2
  · simp only [if_neg h]
    by_cases hbit : cursor.bit ≥ 8#u8
    · have hbad : ¬cursor.bit.val < 8 := by scalar_tac
      simp [read_bit_ordered, hbit, hbad, spec_ok]
    · have hbyte : cursor.byte ≥ input.len := by scalar_tac
      simp only [read_bit_ordered, hbit, hbyte, ↓reduceIte]
      by_cases heq : cursor.byte = input.len <;>
        by_cases hzero : cursor.bit = 0#u8 <;>
        simp_all [spec_ok]

#print axioms read_ordered_bits_spec
#print axioms read_bit_ordered_spec

end RustHammer.Proofs
