import RustHammer.DependentSpec
import RustHammer.BindProofs
import RustHammer.CompositionProofs
import RustHammer.RepeatProofs

open RustHammer.Code.grammar.bytes
  RustHammer.Code.grammar.numeric
  RustHammer.Code.grammar.repeat
  RustHammer.Code.grammar.transform
  RustHammer.Code.input_types

open Aeneas Aeneas.Std Result WP

namespace RustHammer.Proofs
open Code

private abbrev countInst :=
  dependent_examples.CountPrefix.Insts.RusthammerParser_traitsParserInputUsize
private abbrev checkInst :=
  dependent_examples.count_parser.closure.Insts.CoreOpsFunctionFnTupleU64ResultUsizeTuple
private abbrev payloadFactory :=
  dependent_examples.payload.closure.Insts.CoreOpsFunctionFnTupleUsizeTakeAligned
private abbrev fieldsFactory :=
  dependent_examples.fields.closure.Insts.CoreOpsFunctionFnTupleUsizeRepeatBits

private theorem fixed_bits_spec (width : U8) (hwidth : width.val ≤ 64) :
    dependent_examples.fixed_bits width ⦃ result => result = { width } ⦄ := by
  unfold dependent_examples.fixed_bits
  step with bits_new_spec width as ⟨configured, hconfigured⟩
  simp only [Spec.bitsNewOutcome, if_pos hwidth] at hconfigured
  simp [hconfigured, spec_ok]

private def checkedCount (value : U64) (result : core.result.Result Usize Unit) : Prop :=
  if value.val ≤ 64 then ∃ count, result = .Ok count ∧ count.val = value.val
  else result = .Err ()

private theorem checked_count_spec (value : U64) :
    checkInst.call () value ⦃ result => checkedCount value result ⦄ := by
  change dependent_examples.count_parser.closure.Insts.CoreOpsFunctionFnTupleU64ResultUsizeTuple.call
    () value ⦃ result => checkedCount value result ⦄
  simp only [dependent_examples.count_parser.closure.Insts.CoreOpsFunctionFnTupleU64ResultUsizeTuple.call]
  by_cases h : value.val ≤ 64
  · have hv : value ≤ 64#u64 := by scalar_tac
    simp only [if_pos hv]
    step with UScalar.cast_inBounds_spec .Usize value (by scalar_tac) as ⟨count, hcount⟩
    simp only [checkedCount, if_pos h]
    exact ⟨count, rfl, hcount⟩
  · have hv : ¬value ≤ 64#u64 := by scalar_tac
    simp [hv, checkedCount, h, spec_ok]

private theorem count_prefix_decode (input : Slice U8) (cursor : Cursor)
    (outcome : Spec.ParseResult Usize)
    (h : Spec.tryMap (fun start => Spec.bitsOutcome input start 8#u8)
      checkedCount cursor outcome) : Spec.countPrefix input cursor outcome := by
  rcases h with ⟨raw, hraw, hrest⟩
  by_cases hv : Spec.validCursor input cursor
  · simp only [Spec.bitsOutcome, if_pos hv, UScalar.ofNatCore_val_eq] at hraw
    by_cases hfit : Spec.position cursor + 8 ≤ 8 * input.val.length
    · simp only [if_pos hfit] at hraw
      rcases hraw with ⟨next, value, rfl, hn, hpos, hvalue⟩
      simp only [] at hrest
      rcases hrest with ⟨converted, hconverted, hrest⟩
      have hvalue' : value.val = Spec.countValue input cursor := hvalue
      by_cases hcount : value.val ≤ 64
      · simp only [checkedCount, if_pos hcount] at hconverted
        rcases hconverted with ⟨count, rfl, hc⟩
        simp only at hrest
        have hallowed : Spec.countValue input cursor ≤ 64 := by omega
        simp only [Spec.countPrefix, if_pos hv, if_pos hfit, if_pos hallowed]
        exact ⟨next, count, hrest, hn, hpos, hc.trans hvalue'⟩
      · simp only [checkedCount, if_neg hcount] at hconverted
        subst converted
        have hallowed : ¬Spec.countValue input cursor ≤ 64 := by omega
        simpa only [Spec.countPrefix, if_pos hv, if_pos hfit, if_neg hallowed] using hrest
    · simp only [if_neg hfit] at hraw
      subst raw
      simp only [Spec.countPrefix, if_pos hv, if_neg hfit]
      exact hrest
  · simp only [Spec.bitsOutcome, if_neg hv] at hraw
    subst raw
    simp only [Spec.countPrefix, if_neg hv]
    exact hrest

/-- Checked decoding and the cast are total, including all invalid/truncated inputs. -/
theorem count_prefix_with_spec (input : Slice U8) (cursor : Cursor) :
    countInst.parse_with () input cursor ByteOrder.Big
      ⦃ result => Spec.countPrefix input cursor result ⦄ := by
  change dependent_examples.CountPrefix.Insts.RusthammerParser_traitsParserInputUsize.parse_with () input cursor ByteOrder.Big
    ⦃ result => Spec.countPrefix input cursor result ⦄
  rw [dependent_examples.CountPrefix.Insts.RusthammerParser_traitsParserInputUsize.parse_with]
  unfold dependent_examples.count_parser
  step with fixed_bits_spec 8#u8 (by decide) as ⟨configured, hconfigured⟩
  simp only [hconfigured]
  step with try_map_with_spec Bits.Insts.RusthammerParser_traitsParserInputU64 checkInst
    { parser := { width := 8#u8 }, map := () } input cursor ByteOrder.Big
    (fun start => Spec.bitsOutcome input start 8#u8) checkedCount
    (bits_with_spec { width := 8#u8 } input cursor (by decide))
    (fun _ value _ => checked_count_spec value) as ⟨outcome, houtcome⟩
  exact count_prefix_decode input cursor outcome houtcome

/-- The extracted application uses the generic Bind contract, with a proven
factory and the already verified borrowed-payload parser. -/
theorem dependent_payload_spec (input : Slice U8) (cursor : Cursor) :
    dependent_examples.payload input cursor ByteOrder.Big
      ⦃ result => Spec.dependentPayload input cursor result ⦄ := by
  unfold dependent_examples.payload
  apply bind_with_spec countInst payloadFactory TakeAligned.Insts.RusthammerParser_traitsParserInputSharedInputSliceU8
    { parser := (), «then» := () } input cursor ByteOrder.Big
    (fun start => Spec.countPrefix input start)
    (fun count start => (Spec.takeAlignedOutcome input start count))
    (fun count parser => parser = { count }) (count_prefix_with_spec input cursor)
  · intro next value _
    simp [dependent_examples.payload.closure.Insts.CoreOpsFunctionFnTupleUsizeTakeAligned.call, spec_ok]
  · intro next value child _ hc
    subst child
    exact take_aligned_with_spec { count := value } input next

theorem dependent_fields_spec (input : Slice U8) (cursor : Cursor) :
    dependent_examples.fields input cursor ByteOrder.Big
      ⦃ result => Spec.dependentFields input cursor result ⦄ := by
  unfold dependent_examples.fields
  step with fixed_bits_spec 4#u8 (by decide) as ⟨configured, hconfigured⟩
  simp only [hconfigured]
  apply bind_with_spec countInst fieldsFactory (Repeat.Insts.RusthammerParser_traitsParserInputVec Bits.Insts.RusthammerParser_traitsParserInputU64)
    { parser := (), «then» := { width := 4#u8 } } input cursor ByteOrder.Big
    (fun start => Spec.countPrefix input start)
    (fun count start => Spec.repeatN
      (fun pos => Spec.bitsOutcome input pos 4#u8) count.val start)
    (fun count parser => parser = { parser := { width := 4#u8 }, bounds := { min := count, max := some count } })
    (count_prefix_with_spec input cursor)
  · intro next value _
    simp [dependent_examples.fields.closure.Insts.CoreOpsFunctionFnTupleUsizeRepeatBits.call,
      Repeat.exact, RepeatBounds.exact, spec_ok]
  · intro next count child _ hc
    subst child
    exact repeat_exact_with_spec Bits.Insts.RusthammerParser_traitsParserInputU64 { width := 4#u8 } count input next ByteOrder.Big
      (fun pos => Spec.bitsOutcome input pos 4#u8)
      (fun pos => bits_with_spec { width := 4#u8 } input pos (by decide))

theorem count_prefix_success (input : Slice U8) (cursor next : Cursor) (count : Usize)
    (h : Spec.countPrefix input cursor (.Ok (next, count))) :
    Spec.validCursor input cursor ∧ Spec.validCursor input next ∧
    Spec.position next = Spec.position cursor + 8 ∧ count.val = Spec.countValue input cursor ∧ count.val ≤ 64 := by
  unfold Spec.countPrefix at h
  split at h
  next hv =>
    split at h
    next hfit =>
      split at h
      next hallowed =>
        rcases h with ⟨after, value, heq, ha, hp, hvv⟩
        cases heq
        exact ⟨hv, ha, hp, hvv, by omega⟩
      next => cases h
    next => simp_all []
  next => cases h

/-- Successful byte payloads have exactly the advertised bounded length, preserve
the original contents, and consume one count byte plus that many payload bytes. -/
theorem dependent_payload_success (input : Slice U8) (cursor next : Cursor)
    (payload : Slice U8) (h : Spec.dependentPayload input cursor (.Ok (next, payload))) :
    cursor.bit.val = 0 ∧ next.bit.val = 0 ∧
    payload.val.length = Spec.countValue input cursor ∧ payload.val.length ≤ 64 ∧
    next.byte.val = cursor.byte.val + 1 + payload.val.length ∧
    payload.val = (input.val.drop (cursor.byte.val + 1)).take (Spec.countValue input cursor) := by
  rcases bind_success_children _ _ cursor next payload h with ⟨middle, count, hc, hp⟩
  rcases count_prefix_success input cursor middle count hc with ⟨hv, hm, hpos, hvalue, hbound⟩
  have hbody := hp
  unfold Spec.takeAlignedOutcome at hbody
  split at hbody
  next hvalid =>
    split at hbody
    next haligned =>
      split at hbody
      next hfit =>
        rcases hbody with ⟨after, bytes, heq, hbyte, hbit, hbytes⟩
        cases heq
        have hstart : cursor.bit.val = 0 ∧ middle.byte.val = cursor.byte.val + 1 := by
          simp only [Spec.validCursor, Spec.position] at hv hpos
          omega
        have hlen : payload.val.length = count.val := by
          rw [hbytes, List.length_take, List.length_drop, Nat.min_eq_left (by omega)]
        refine ⟨hstart.1, by simp [hbit], hlen.trans hvalue, by omega, ?_, ?_⟩
        · omega
        · simpa [hstart.2, hvalue] using hbytes
      next => cases hbody
    next => cases hbody
  next => cases hbody

/-- Counted elements consume four bits each, including when the final cursor is
inside a byte. Their ordered values are specified by the repetition relation. -/
theorem dependent_fields_success (input : Slice U8) (cursor next : Cursor)
    (values : alloc.vec.Vec U64) (h : Spec.dependentFields input cursor (.Ok (next, values))) :
    values.val.length = Spec.countValue input cursor ∧ values.val.length ≤ 64 ∧
    Spec.position next = Spec.position cursor + 8 + values.val.length * 4 := by
  rcases bind_success_children _ _ cursor next values h with ⟨middle, count, hc, hp⟩
  rcases count_prefix_success input cursor middle count hc with ⟨_, _, hpos, hvalue, hbound⟩
  rcases hp with ⟨hlen, hchain⟩
  have hconsume := repetitions_advance _ 4 middle next values.val
    (by
      intro start after value h
      have hbits := h
      unfold Spec.bitsOutcome at hbits
      split at hbits
      · split at hbits
        · rcases hbits with ⟨_, _, heq, _, hp, _⟩; cases heq; exact hp
        · cases hbits
      · cases hbits) hchain
  exact ⟨hlen.trans hvalue, by omega, by omega⟩

end RustHammer.Proofs
