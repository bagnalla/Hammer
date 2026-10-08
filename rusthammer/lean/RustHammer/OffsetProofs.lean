import RustHammer.OffsetSpec
import RustHammer.SeekProperties
import RustHammer.BindProofs
import RustHammer.SelectionProofs
import RustHammer.ByteProofs

open Aeneas Aeneas.Std Result WP
open RustHammer.Code.input_types RustHammer.Code.grammar.position
open RustHammer.Code.grammar.sequence RustHammer.Code.grammar.numeric
open RustHammer.Code.grammar.bytes RustHammer.Code.parser_traits

namespace RustHammer.Offset
open Code Proofs

private abbrev factory :=
  offset_example.payload.closure.Insts.CoreOpsFunctionFnTupleU8RightSeekTakeAligned
private abbrev seekInst : DirectParser Seek Cursor := Seeking.evalInst Direct
private abbrev takeInst := TakeAligned.Insts.RusthammerParserInputSharedInputSliceU8
private abbrev bodyInst := Right.Insts.RusthammerParser seekInst takeInst

private def constructed (distance : U8) (child : Right Seek TakeAligned) : Prop :=
  ∃ offset, offset.val = (distance.val : Int) * 8 ∧
    child = { first := ⟨.Relative offset⟩, second := { count := 2#usize } }

/-- The shared example's cast and multiplication are lossless and cannot fail. -/
theorem factory_spec (distance : U8) :
    factory.call () distance ⦃ child => constructed distance child ⦄ := by
  change offset_example.payload.closure.Insts.CoreOpsFunctionFnTupleU8RightSeekTakeAligned.call
    () distance ⦃ child => constructed distance child ⦄
  unfold offset_example.payload.closure.Insts.CoreOpsFunctionFnTupleU8RightSeekTakeAligned.call
  step with UScalar.hcast_inBounds_spec .Isize distance (by scalar_tac) as ⟨signed, hsigned⟩
  step with IScalar.mul_spec (x := signed) (y := 8#isize)
    (by scalar_tac) (by scalar_tac) as ⟨offset, hoffset⟩
  step with Seeking.relative_spec offset as ⟨seek, hseek⟩
  exact ⟨offset, by scalar_tac, by simp only [hseek]⟩

/-- The extracted application is proved by the ordinary Bind/Right contracts
and the backend-generic Seek proof; no separate parser model is substituted. -/
theorem payload_spec (input : Slice U8) (cursor : Cursor) (status : InputStatus) :
    offset_example.payload input cursor (Spec.defaultContext status)
      ⦃ result => payload input cursor status result ⦄ := by
  simp only [offset_example.payload, grammar.sequence.bind, bind_ok]
  apply bind_with_spec Byte.Insts.RusthammerParserInputU8 factory bodyInst
    { parser := (), «then» := () } input cursor (Spec.defaultContext status)
    (fun start => Partial.primitive status (Spec.byteOutcome input start))
    (fun distance start => body input start distance.val status) constructed
    (byte_with_spec input cursor status)
  · intro _ value _
    exact factory_spec value
  · rintro next distance child _ ⟨offset, hoffset, rfl⟩
    apply right_with_spec seekInst takeInst
      { first := ⟨.Relative offset⟩, second := { count := 2#usize } }
      input next (Spec.defaultContext status)
      (fun start => jump input start distance.val status)
      (fun start => Partial.primitive status (Spec.takeAlignedOutcome input start 2#usize))
    · intro start
      step with Seeking.with_spec ⟨.Relative offset⟩ input start (Spec.defaultContext status)
        (by trivial) as ⟨result, hresult⟩
      have h := (Seeking.relative_outcome offset input.val.length start status result).mp hresult
      simpa only [jump, hoffset, Int.mul_comm] using h
    · intro start
      exact take_aligned_with_spec { count := 2#usize } input start status

private theorem primitive_success {α : Type} (status : InputStatus)
    (contract : Spec.ParseResult α → Prop) (next : Cursor) (value : α)
    (h : Partial.primitive status contract (.Success next value)) : contract (.Ok (next, value)) := by
  rcases h with ⟨parsed, hparsed, heq⟩
  cases parsed with
  | Ok pair => cases pair; cases status <;> simp_all [Partial.primitiveResult, Spec.completedResult]
  | Err error => cases status <;> cases error <;> cases heq

theorem jump_success (input : Slice U8) (cursor next value : Cursor) (distance : Nat)
    (status : InputStatus) (h : jump input cursor distance status (.Success next value)) :
    Spec.validCursor input cursor ∧ Spec.validCursor input next ∧ value = next ∧
      Spec.position next = Spec.position cursor + 8 * distance := by
  rcases h with ⟨raw, hraw, heq⟩
  cases raw with
  | Err error => cases status <;> cases error <;> cases heq
  | Ok destination =>
    have heq' : next = destination ∧ value = destination := by
      cases status <;> simpa [Partial.primitiveResult, Seeking.reported, Spec.completedResult] using heq
    rcases heq' with ⟨hnext, hvalue⟩
    subst destination
    obtain ⟨hv, hn, hp⟩ := (Seeking.target_success input.val.length cursor next _).mp hraw
    exact ⟨hv, hn, hvalue, by omega⟩

/-- Every successful parse selects exactly the two original bytes addressed by
the displacement field, ends just after them, and requires byte alignment.
Borrow identity is checked by native tests; the Lean slice model is by value. -/
theorem payload_success (input : Slice U8) (cursor next : Cursor) (status : InputStatus)
    (bytes : Slice U8) (h : payload input cursor status (.Success next bytes)) :
    cursor.bit.val = 0 ∧ next.bit.val = 0 ∧ bytes.val.length = 2 ∧
      next.byte.val = cursor.byte.val + 1 + Spec.unsignedBits input (Spec.position cursor) 8 + 2 ∧
      bytes.val = (input.val.drop
        (cursor.byte.val + 1 + Spec.unsignedBits input (Spec.position cursor) 8)).take 2 := by
  obtain ⟨middle, distance, hbyte, hbody⟩ := bind_success_children _ _ cursor next bytes h
  obtain ⟨destination, saved, hjump, htake⟩ := right_success_children _ _ middle next bytes hbody
  obtain ⟨hv, hm, hpos, hvalue⟩ := byte_success input cursor middle distance status hbyte
  obtain ⟨_, hd, _, hdpos⟩ := jump_success input middle destination saved distance.val status hjump
  have hraw := primitive_success status _ next bytes htake
  unfold Spec.takeAlignedOutcome at hraw
  split at hraw
  next hvalid =>
    split at hraw
    next haligned =>
      split at hraw
      next hfit =>
        rcases hraw with ⟨after, payload, heq, hnext, hbit, hbytes⟩
        cases heq
        simp only [UScalar.ofNatCore_val_eq] at hfit hnext hbytes
        have hpositions : cursor.bit.val = 0 ∧
            destination.byte.val = cursor.byte.val + 1 + distance.val := by
          simp only [Spec.validCursor, Spec.position] at hv hm hd hpos hdpos
          omega
        have hlength : bytes.val.length = 2 := by
          rw [hbytes, List.length_take, List.length_drop]
          omega
        exact ⟨hpositions.1, by simp [hbit], hlength, by omega,
          by simpa only [hpositions.2, hvalue] using hbytes⟩
      next => cases hraw
    next => cases hraw
  next => cases hraw

end RustHammer.Offset
