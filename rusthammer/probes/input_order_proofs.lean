import InputOrder

open Aeneas Aeneas.Std Result WP

namespace InputOrder.Proofs

/-- Mathematical position only; equal ranks need not be equal physical cursors. -/
def rank (cursor : Cursor) : Nat :=
  8 * cursor.byte.val + cursor.high.val + cursor.low.val

def valid (length : Nat) (cursor : Cursor) : Prop :=
  cursor.high.val + cursor.low.val < 8 ∧ rank cursor ≤ 8 * length

/-- The exact physical transition, including which edge was consumed. -/
def segment (cursor : Cursor) (take : U8) (order : BitOrder) (next : Cursor) : Prop :=
  if cursor.high.val + cursor.low.val + take.val = 8 then
    next.byte.val = cursor.byte.val + 1 ∧ next.high.val = 0 ∧ next.low.val = 0
  else
    next.byte = cursor.byte ∧
      match order with
      | .HighFirst => next.high.val = cursor.high.val + take.val ∧ next.low = cursor.low
      | .LowFirst => next.high = cursor.high ∧ next.low.val = cursor.low.val + take.val

/-- The actual extracted arithmetic is safe, preserves normalized validity,
advances by exactly `take` bits, and consumes only the selected edge. -/
theorem advance_segment_spec (length : Usize) (cursor : Cursor) (take : U8)
    (order : BitOrder) (hshape : cursor.high.val + cursor.low.val < 8)
    (hbyte : cursor.byte.val < length.val)
    (htake : cursor.high.val + cursor.low.val + take.val ≤ 8) :
    advance_segment cursor take order
      ⦃ next => valid length.val next ∧ rank next = rank cursor + take.val ∧
        segment cursor take order next ⦄ := by
  unfold advance_segment
  step as ⟨used, hused⟩
  step as ⟨total, htotal⟩
  by_cases hfull : total = 8#u8
  · simp only [hfull, ↓reduceIte]
    step as ⟨byte, hnext⟩
    have hsum : cursor.high.val + cursor.low.val + take.val = 8 := by scalar_tac
    simp only [valid, rank, segment, if_pos hsum]
    scalar_tac
  · simp only [hfull, ↓reduceIte]
    have hsum : cursor.high.val + cursor.low.val + take.val ≠ 8 := by scalar_tac
    cases order <;> simp only
    · step as ⟨high, hhigh⟩
      simp only [valid, rank, segment, if_neg hsum]
      scalar_tac
    · step as ⟨low, hlow⟩
      simp only [valid, rank, segment, if_neg hsum]
      scalar_tac

/-- An ordering scope passes the child the new order and the original finality.
The physical cursor is unchanged on entry; the caller's context is a value. -/
theorem with_order_eq {P O : Type} (inst : Parser P O) (parser : WithOrder P)
    (input : Slice U8) (cursor : Cursor) (ctx : Context) :
    WithOrder.Insts.Input_orderParser.parse_with inst parser input cursor ctx =
      inst.parse_with parser.child input cursor { ctx with order := parser.order } := by
  rfl

#print axioms advance_segment_spec
#print axioms with_order_eq

end InputOrder.Proofs
