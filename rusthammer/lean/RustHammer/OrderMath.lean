import RustHammer.OrderSpec
import RustHammer.BitsProofs

open RustHammer.Code.input_types

open Aeneas Aeneas.Std

namespace RustHammer.Ordering
open Code

@[simp] theorem unsigned_zero (input : Slice U8) (order : Order) (start : Nat) :
    unsigned input order start 0 = 0 := by rw [unsigned]; rfl

theorem fragment_width_bounds (start width : Nat) (hw : 0 < width) :
    0 < fragmentWidth start width ∧ fragmentWidth start width ≤ width ∧
      fragmentWidth start width ≤ 8 - start % 8 := by
  have := Nat.mod_lt start (by decide : 0 < 8)
  unfold fragmentWidth
  omega

theorem unsigned_bound (input : Slice U8) (order : Order) (start width : Nat) :
    unsigned input order start width < 2 ^ width := by
  induction width using Nat.strong_induction_on generalizing start with
  | h width ih =>
    rw [unsigned]
    split
    · subst width; simp
    · rename_i hzero
      have ht := fragment_width_bounds start width (by omega)
      have htail := ih (width - fragmentWidth start width) (by omega)
        (start + fragmentWidth start width)
      have hpart := Proofs.unsignedBits_lt_pow input
        (fragmentStart order.bit start (fragmentWidth start width)) (fragmentWidth start width)
      have hexp : width = fragmentWidth start width + (width - fragmentWidth start width) := by omega
      have hpow : 2 ^ width = 2 ^ fragmentWidth start width * 2 ^ (width - fragmentWidth start width) := by
        conv_lhs => rw [hexp, Nat.pow_add]
      cases order.byte <;> dsimp <;> rw [hpow] <;> nlinarith

theorem unsigned_bits_split (input : Slice U8) (start first rest : Nat) :
    Spec.unsignedBits input start (first + rest) =
      Spec.unsignedBits input start first * 2 ^ rest +
        Spec.unsignedBits input (start + first) rest := by
  induction first generalizing start with
  | zero => simp [Spec.unsignedBits]
  | succ first ih =>
    simp only [Nat.succ_add, Spec.unsignedBits]
    rw [ih, Nat.pow_add]
    have heq : start + 1 + first = start + (first + 1) := by omega
    rw [heq]
    ring

/-- Default ordering preserves the existing positional-binary specification. -/
theorem unsigned_default (input : Slice U8) (start width : Nat) :
    unsigned input Order.DEFAULT start width = Spec.unsignedBits input start width := by
  induction width using Nat.strong_induction_on generalizing start with
  | h width ih =>
    rw [unsigned]
    split
    · subst width; simp [Spec.unsignedBits]
    · rename_i hzero
      have ht := fragment_width_bounds start width (by omega)
      dsimp only
      rw [ih (width - fragmentWidth start width) (by omega)]
      simp only [Order.DEFAULT, fragmentStart]
      have hf : 8 * (start / 8) + start % 8 = start := by omega
      rw [hf]
      have heq : fragmentWidth start width + (width - fragmentWidth start width) = width := by omega
      simpa only [heq] using (unsigned_bits_split input start (fragmentWidth start width)
        (width - fragmentWidth start width)).symm

@[simp] theorem outcome_default (input : Slice U8) (cursor : Cursor) (width : U8)
    (result : Spec.ParseResult U64) :
    outcome input cursor width Order.DEFAULT result ↔ Spec.bitsOutcome input cursor width result := by
  simp only [outcome, success, Spec.bitsOutcome, Spec.bitsSuccess, unsigned_default]

end RustHammer.Ordering
