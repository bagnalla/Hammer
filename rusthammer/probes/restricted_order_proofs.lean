import RestrictedOrder

open Aeneas Aeneas.Std Result WP

namespace RestrictedOrder.Proofs
noncomputable section
open Classical

def valid (length : Usize) (cursor : Cursor) : Prop :=
  cursor.bit < 8#u8 ∧
    (cursor.byte < length ∨ (cursor.byte = length ∧ cursor.bit = 0#u8))

def guard (length : Usize) (cursor : Cursor) : Option ParseError :=
  if valid length cursor then
    if cursor.bit = 0#u8 then none else some .Unaligned
  else some .InvalidCursor

def finish {α : Type} (length : Usize) (changed : Bool) (child : Outcome α) : Outcome α :=
  if changed then
    match child with
    | .Success next value =>
      match guard length next with
      | none => .Success next value
      | some error => .Error error
    | .Error error => .Error error
    | .NeedMore => .NeedMore
  else child

/-- Child termination/semantics is required only when the entry guard permits it. -/
def scope {α : Type} (length : Usize) (changed : Bool) (cursor : Cursor)
    (child : Outcome α → Prop) (outcome : Outcome α) : Prop :=
  if changed then
    match guard length cursor with
    | some error => outcome = .Error error
    | none => ∃ result, child result ∧ outcome = finish length true result
  else child outcome

theorem cursor_valid_spec (length : Usize) (cursor : Cursor) :
    Cursor.valid cursor length ⦃ b => b = decide (valid length cursor) ⦄ := by
  unfold Cursor.valid valid
  split <;> simp_all [spec_ok]
  split <;> simp_all [spec_ok]
  split <;> simp_all [spec_ok]

theorem boundary_error_spec (length : Usize) (cursor : Cursor) :
    boundary_error length cursor ⦃ result => result = guard length cursor ⦄ := by
  unfold boundary_error
  step with cursor_valid_spec length cursor as ⟨b, hb⟩
  by_cases hv : valid length cursor
  · simp only [hb, hv, decide_true, ↓reduceIte]
    by_cases hz : cursor.bit = 0#u8 <;> simp [hz, guard, hv, spec_ok]
  · simp [hb, hv, guard, spec_ok]

theorem bit_order_ne_spec (first second : BitOrder) :
    core.cmp.PartialEq.ne.trait_default BitOrder.Insts.CoreCmpPartialEqBitOrder first second
      ⦃ result => result = decide (first ≠ second) ⦄ := by
  cases first <;> cases second <;>
    simp [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
      BitOrder.Insts.CoreCmpPartialEqBitOrder.eq, BitOrder.read_discriminant, spec_ok]

theorem finish_scope_spec {α : Type} (length : Usize) (changed : Bool) (child : Outcome α) :
    finish_scope length changed child ⦃ result => result = finish length changed child ⦄ := by
  unfold finish_scope
  cases changed with
  | false => simp [finish, spec_ok]
  | true =>
    simp only [↓reduceIte]
    cases child with
    | Error error => simp [finish, spec_ok]
    | NeedMore => simp [finish, spec_ok]
    | Success next value =>
      step with boundary_error_spec length next as ⟨error, herror⟩
      cases hg : guard length next <;> simp [herror, hg, finish, spec_ok]

/-- Total generic scope contract with exact error precedence, successful-exit
validation, unchanged finality, and unchanged outcomes when direction is kept. -/
theorem with_order_spec {P α : Type} (inst : Parser P α) (parser : WithOrder P)
    (input : Slice U8) (cursor : Cursor) (ctx : ParseContext)
    (child : Outcome α → Prop)
    (hp : (parser.order.bit = ctx.order.bit ∨ guard input.len cursor = none) →
      inst.parse_with parser.child input cursor { ctx with order := parser.order }
        ⦃ result => child result ⦄) :
    WithOrder.Insts.Restricted_orderParser.parse_with inst parser input cursor ctx
      ⦃ result => scope input.len (decide (parser.order.bit ≠ ctx.order.bit)) cursor child result ⦄ := by
  unfold WithOrder.Insts.Restricted_orderParser.parse_with
  step with bit_order_ne_spec parser.order.bit ctx.order.bit as ⟨changed, hchanged⟩
  by_cases hsame : parser.order.bit = ctx.order.bit
  · have hc : changed = false := by simp [hchanged, hsame]
    simp only [hc, Bool.false_eq_true, ↓reduceIte]
    step with hp (Or.inl hsame) as ⟨result, hresult⟩
    step with finish_scope_spec input.len false result as ⟨outcome, houtcome⟩
    simpa [scope, hsame, finish, houtcome] using hresult
  · have hc : changed = true := by simp [hchanged, hsame]
    simp only [hc, ↓reduceIte]
    step with boundary_error_spec input.len cursor as ⟨error, herror⟩
    cases hg : guard input.len cursor with
    | some error => simp [herror, hg, scope, hsame, spec_ok]
    | none =>
      simp only [herror, hg]
      step with hp (Or.inr hg) as ⟨result, hresult⟩
      step with finish_scope_spec input.len true result as ⟨outcome, houtcome⟩
      simpa [scope, hsame, hg] using (show ∃ r, child r ∧ outcome = finish input.len true r
        from ⟨result, hresult, houtcome⟩)

/-- Rejected entries need no assumption about the uncalled parser. -/
theorem with_order_blocked {P α : Type} (inst : Parser P α) (parser : WithOrder P)
    (input : Slice U8) (cursor : Cursor) (ctx : ParseContext) (error : ParseError)
    (hchanged : parser.order.bit ≠ ctx.order.bit) (hguard : guard input.len cursor = some error) :
    WithOrder.Insts.Restricted_orderParser.parse_with inst parser input cursor ctx
      ⦃ result => result = .Error error ⦄ := by
  have hp : (parser.order.bit = ctx.order.bit ∨ guard input.len cursor = none) →
      inst.parse_with parser.child input cursor { ctx with order := parser.order }
        ⦃ _ => True ⦄ := by
    intro h
    rcases h with h | h
    · exact False.elim (hchanged h)
    · simp [hguard] at h
  simpa [scope, hchanged, hguard] using with_order_spec inst parser input cursor ctx (fun _ => True) hp

theorem finish_success_aligned {α : Type} (length : Usize) (child : Outcome α)
    (next : Cursor) (value : α) (h : finish length true child = .Success next value) :
    valid length next ∧ next.bit = 0#u8 ∧ child = .Success next value := by
  cases child with
  | Error error => simp [finish] at h
  | NeedMore => simp [finish] at h
  | Success endCursor output =>
    by_cases hv : valid length endCursor
    · by_cases hz : endCursor.bit = 0#u8
      · have heq : endCursor = next ∧ output = value := by simpa [finish, guard, hv, hz] using h
        rcases heq with ⟨rfl, rfl⟩
        exact ⟨hv, hz, rfl⟩
      · simp [finish, guard, hv, hz] at h
    · simp [finish, guard, hv] at h

theorem guard_none_iff (length : Usize) (cursor : Cursor) :
    guard length cursor = none ↔ valid length cursor ∧ cursor.bit = 0#u8 := by
  by_cases hv : valid length cursor
  · by_cases hz : cursor.bit = 0#u8 <;> simp [guard, hv, hz]
  · simp [guard, hv]

/-- Combined with `with_order_spec`, every accepted direction-changing scope
has valid, aligned entry and exit, regardless of its child's output type. -/
theorem scope_success_aligned {α : Type} (length : Usize) (cursor next : Cursor)
    (value : α) (child : Outcome α → Prop)
    (h : scope length true cursor child (.Success next value)) :
    valid length cursor ∧ cursor.bit = 0#u8 ∧ valid length next ∧ next.bit = 0#u8 := by
  simp only [scope, ↓reduceIte] at h
  cases hg : guard length cursor with
  | some error => simp [hg] at h
  | none =>
    simp only [hg] at h
    rcases h with ⟨result, _, heq⟩
    have hstart := (guard_none_iff length cursor).mp hg
    have hend := finish_success_aligned length result next value heq.symm
    exact ⟨hstart.1, hstart.2, hend.1, hend.2.1⟩

end

#print axioms cursor_valid_spec
#print axioms boundary_error_spec
#print axioms bit_order_ne_spec
#print axioms finish_scope_spec
#print axioms with_order_spec
#print axioms with_order_blocked
#print axioms finish_success_aligned
#print axioms guard_none_iff
#print axioms scope_success_aligned

end RestrictedOrder.Proofs
