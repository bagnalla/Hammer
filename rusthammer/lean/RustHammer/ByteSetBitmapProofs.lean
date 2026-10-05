import RustHammer.ByteSetSpec
import Mathlib.Data.Nat.Bitwise

open Aeneas Aeneas.Std Result WP

namespace RustHammer.Proofs
open Code

private theorem bitmap_index_lt (byte : U8) : byte.val / 64 < 4 := by
  have h := byte.hmax
  scalar_tac

private theorem bitmap_bit_lt (byte : U8) : byte.val % 64 < 64 := by
  omega

private theorem bitmap_mask_value (byte bit : U8) (mask : U64)
    (hbit : bit.val = byte.val % 64)
    (hmask : mask.val = (1 <<< bit.val) % U64.size) :
    mask.val = 2 ^ (byte.val % 64) := by
  have hpow : 2 ^ (byte.val % 64) < 2 ^ 64 :=
    Nat.pow_lt_pow_right (by decide) (bitmap_bit_lt byte)
  have hsize : U64.size = 2 ^ 64 := by simp [U64.size, U64.numBits]
  calc
    mask.val = (2 ^ (byte.val % 64)) % (2 ^ 64) := by
      simpa only [Nat.shiftLeft_eq, Nat.one_mul, hbit, hsize] using hmask
    _ = 2 ^ (byte.val % 64) := Nat.mod_eq_of_lt hpow

/-- Updating one word by OR-ing one bit adds exactly the requested byte. -/
private theorem bitmap_insert (words : Array U64 4#usize)
    (byte value : U8) (index : Usize) (old mask : U64)
    (hindex : index.val = byte.val / 64)
    (hold : old = words[index.val]!)
    (hmask : mask.val = 2 ^ (byte.val % 64)) :
    Spec.bitmapMember (words.set index (old ||| mask)) value ↔
      value = byte ∨ Spec.bitmapMember words value := by
  have hbound : value.val / 64 < words.length := by
    simpa using bitmap_index_lt value
  unfold Spec.bitmapMember
  by_cases hword : index.val = value.val / 64
  · rw [Array.getElem!_Nat_set_eq words index _ _ ⟨hword, hbound⟩]
    have hold' : old = words[value.val / 64]! := by simpa [hword] using hold
    have hbyte : byte.val % 64 = value.val % 64 ↔ value = byte := by
      constructor
      · intro hbit
        apply UScalar.eq_of_val_eq
        omega
      · intro heq
        subst value
        rfl
    simp only [UScalar.val_or, Nat.testBit_or, Bool.or_eq_true, hmask,
      Nat.testBit_two_pow, decide_eq_true_eq, hold', hbyte]
    exact or_comm
  · rw [Array.getElem!_Nat_set_ne words index _ _ hword]
    have hne : value ≠ byte := by
      intro h
      subst value
      exact hword hindex
    simp [hne]

/-- Construction terminates by the remaining slice length. Its loop invariant
says the current bitmap represents precisely the processed prefix. -/
theorem byte_set_new_spec (bytes : Slice U8) :
    ByteSet.new bytes ⦃ set => Spec.bitmapRepresents set bytes.val ⦄ := by
  unfold ByteSet.new ByteSet.new_loop
  suffices h : loop
      (fun (words, index) => ByteSet.new_loop.body bytes words index)
      (Array.repeat 4#usize 0#u64, 0#usize)
      ⦃ words => ∀ value, Spec.bitmapMember words value ↔ value ∈ bytes.val ⦄ by
    step with h
    assumption
  apply loop.spec_decr_nat (fun state => bytes.val.length - state.2.val)
    (fun (words, index) => index.val ≤ bytes.val.length ∧
      ∀ value, Spec.bitmapMember words value ↔ value ∈ bytes.val.take index.val)
  · rintro ⟨words, index⟩ ⟨hindex, hprefix⟩
    unfold ByteSet.new_loop.body
    by_cases hlt : index < bytes.len
    · have hlen : index.val < bytes.val.length := by scalar_tac
      simp only [hlt, ↓reduceIte]
      step as ⟨byte, hbyte⟩
      step as ⟨bit, hbit⟩
      step as ⟨mask, hmask⟩
      have hmask' := bitmap_mask_value byte bit mask hbit hmask
      step as ⟨slot, hslot⟩
      step as ⟨slotIndex, hslotIndex⟩
      have hslot' : slotIndex.val = byte.val / 64 := by scalar_tac
      have hbound : slotIndex.val < words.length := by
        simpa [hslot'] using bitmap_index_lt byte
      step as ⟨old, hold⟩
      step as ⟨joined, hjoined⟩
      have hjoined' : joined = old ||| mask := by
        apply UScalar.eq_of_val_eq
        exact hjoined
      step as ⟨updated, hupdated⟩
      step as ⟨next, hnext⟩
      refine ⟨by omega, ?_, by omega⟩
      intro value
      rw [hupdated, hjoined', bitmap_insert words byte value slotIndex old mask
        hslot' (by simpa only [Array.getElem!_Nat_eq,
          getElem!_pos words.val slotIndex.val (by simpa using hbound)] using hold) hmask', hprefix]
      have htake : bytes.val.take (index.val + 1) =
          bytes.val.take index.val ++ [bytes.val[index.val]] :=
        List.take_succ_eq_append_getElem hlen
      simp only [hnext, htake, List.mem_append, List.mem_singleton, hbyte]
      exact or_comm
    · have hend : index.val = bytes.val.length := by scalar_tac
      simp only [hlt, ↓reduceIte, spec_ok]
      simpa [hend] using hprefix
  · refine ⟨by simp, ?_⟩
    intro value
    have hget : (Array.repeat 4#usize 0#u64)[value.val / 64]! = 0#u64 := by
      simp only [Array.getElem!_Nat_eq, Array.repeat_val]
      rw [getElem!_pos _ _ (by simpa using bitmap_index_lt value)]
      exact List.getElem_replicate _
    simp [Spec.bitmapMember, hget]

/-- Lookup is total for every bitmap and byte: the word index is below four and
the shift is below 64. Testing a one-bit mask is mathematical bit membership. -/
theorem byte_set_contains_spec (set : ByteSet) (byte : U8) :
    ByteSet.contains set byte ⦃ result => result = decide (Spec.bitmapMember set.words byte) ⦄ := by
  unfold ByteSet.contains
  step as ⟨slot, hslot⟩
  step as ⟨index, hindex⟩
  have hindex' : index.val = byte.val / 64 := by scalar_tac
  have hbound : index.val < set.words.length := by
    simpa [hindex'] using bitmap_index_lt byte
  step as ⟨word, hword⟩
  step as ⟨bit, hbit⟩
  step as ⟨mask, hmask⟩
  have hmask' := bitmap_mask_value byte bit mask hbit hmask
  step as ⟨selected, hselected⟩
  have hselected' : selected.val = word.val &&& 2 ^ (byte.val % 64) := by
    simpa [hmask'] using hselected
  have hword' : word = set.words[byte.val / 64]! := by
    simpa only [Array.getElem!_Nat_eq, ← hindex',
      getElem!_pos set.words.val index.val (by simpa using hbound)] using hword
  apply Bool.eq_iff_iff.mpr
  simp [Spec.bitmapMember, hselected', Nat.and_two_pow, hword']

end RustHammer.Proofs
