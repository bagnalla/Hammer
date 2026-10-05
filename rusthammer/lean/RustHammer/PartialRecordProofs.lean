import RustHammer.PartialProofs
import RustHammer.RecordProofs
import RustHammer.PartialRecordSpec

open Aeneas Aeneas.Std Result WP

namespace RustHammer.Proofs
open Code
open marker_example record_example

/-- Sequencing readers that only classify exhaustion can reuse their complete
value/position relation. This lifting does not apply to choice or lookahead. -/
theorem sequence_primitive {α β : Type} (status : InputStatus)
    (first : Cursor → Spec.ParseResult α → Prop) (second : Cursor → Spec.ParseResult β → Prop)
    (cursor : Cursor) (outcome : ParseOutcome (α × β))
    (h : Partial.sequence (fun start => Partial.primitive status (first start))
      (fun start => Partial.primitive status (second start)) cursor outcome) :
    Partial.primitive status (Spec.sequence first second cursor) outcome := by
  rcases h with ⟨left, ⟨oldLeft, hleft, rfl⟩, hrest⟩
  cases oldLeft with
  | Err error =>
    refine ⟨.Err error, ⟨.Err error, hleft, rfl⟩, ?_⟩
    cases status <;> cases error <;>
      simpa only [Partial.primitiveResult, Spec.completedResult] using hrest
  | Ok pair =>
    rcases pair with ⟨middle, a⟩
    have heq : Partial.primitiveResult status (.Ok (middle, a)) = .Success middle a := by
      cases status <;> rfl
    rw [heq] at hrest
    rcases hrest with ⟨right, ⟨oldRight, hright, rfl⟩, hrest⟩
    cases oldRight with
    | Err error =>
      refine ⟨.Err error, ⟨.Ok (middle, a), hleft, .Err error, hright, rfl⟩, ?_⟩
      cases status <;> cases error <;>
        simpa only [Partial.primitiveResult, Spec.completedResult] using hrest
    | Ok pair =>
      rcases pair with ⟨last, b⟩
      refine ⟨.Ok (last, (a, b)), ⟨.Ok (middle, a), hleft, .Ok (last, b), hright, rfl⟩, ?_⟩
      cases status <;> simpa only [Partial.primitiveResult, Spec.completedResult] using hrest

private abbrev fieldsParser : Seq Bits (Seq Bits Bits) :=
  { first := Spec.recordParser.version,
    second := { first := Spec.recordParser.flags, second := Spec.recordParser.length } }

private abbrev fieldsInst := Seq.Insts.RusthammerParserInputPair
  Bits.Insts.RusthammerParserInputU64
  (Seq.Insts.RusthammerParserInputPair
    Bits.Insts.RusthammerParserInputU64 Bits.Insts.RusthammerParserInputU64)

private abbrev predicateInst :=
  ParserInputRecordParserRecord.parse_with.closure.Insts.CoreOpsFunctionFnTupleShared0PairU64PairU64U64Bool

theorem record_header_with_spec (input : Slice U8) (cursor : Cursor) (status : InputStatus)
    (hvalid : Spec.validCursor input cursor) (haligned : cursor.bit.val = 0) :
    fieldsInst.parse_with fieldsParser input cursor status
      ⦃ outcome => Partial.primitive status (Spec.recordHeaderOutcome input cursor) outcome ⦄ := by
  let bi := Bits.Insts.RusthammerParserInputU64
  have hv (start : Cursor) := bits_with_spec Spec.recordParser.version input start status (by decide)
  have hf (start : Cursor) := bits_with_spec Spec.recordParser.flags input start status (by decide)
  have hl (start : Cursor) := bits_with_spec Spec.recordParser.length input start status (by decide)
  have htail (start : Cursor) : (Seq.Insts.RusthammerParserInputPair bi bi).parse_with fieldsParser.second input start status
      ⦃ outcome => Partial.primitive status
        (Spec.sequence (fun start => Spec.bitsOutcome input start 5#u8)
          (fun start => Spec.bitsOutcome input start 16#u8) start) outcome ⦄ := by
    step with seq_with_spec bi bi fieldsParser.second input start status
      (fun start => Partial.primitive status (Spec.bitsOutcome input start 5#u8))
      (fun start => Partial.primitive status (Spec.bitsOutcome input start 16#u8)) hf hl
      as ⟨outcome, houtcome⟩
    exact sequence_primitive status _ _ start outcome houtcome
  step with seq_with_spec bi (Seq.Insts.RusthammerParserInputPair bi bi) fieldsParser input cursor status
    (fun start => Partial.primitive status (Spec.bitsOutcome input start 3#u8))
    (fun start => Partial.primitive status (Spec.sequence
      (fun start => Spec.bitsOutcome input start 5#u8)
      (fun start => Spec.bitsOutcome input start 16#u8) start)) hv htail as ⟨outcome, houtcome⟩
  rcases sequence_primitive status _ _ cursor outcome houtcome with ⟨result, hresult, heq⟩
  exact ⟨result, record_fields_decode input cursor result hvalid haligned hresult, heq⟩


theorem marker_with_spec (parser : Marker) (input : Slice U8) (cursor : Cursor)
    (status : InputStatus) (hconfig : Spec.validMarker parser) :
    Marker.Insts.RusthammerParserInputU64.parse_with parser input cursor status
      ⦃ result => Partial.markerOutcome input cursor status result ⦄ := by
  let li := Literal.Insts.RusthammerParserInputU64
  let ci := Choice.Insts.RusthammerParser li li
  let alternatives : Choice Literal Literal := Spec.markerParser.first
  have hchoice (start : Cursor) := choice_with_spec li li alternatives input start status
    (fun start => Partial.primitive status (Spec.literalOutcome input start 16#u8 51966#u64))
    (fun start => Partial.primitive status (Spec.literalOutcome input start 8#u8 202#u64))
    (fun start => literal_with_spec _ input start status (by decide))
    (fun start => literal_with_spec _ input start status (by decide))
  unfold Marker.Insts.RusthammerParserInputU64.parse_with
  rw [hconfig]
  step with seq_with_spec ci End.Insts.RusthammerParserInputTuple
    { first := alternatives, second := () } input cursor status
    (Partial.choice
      (fun start => Partial.primitive status (Spec.literalOutcome input start 16#u8 51966#u64))
      (fun start => Partial.primitive status (Spec.literalOutcome input start 8#u8 202#u64)))
    (fun start => Partial.endOutcome input start status) hchoice
    (fun start => end_with_spec input start status) as ⟨fields, hfields⟩
  cases fields with
  | NeedMore => simp only [spec_ok]; exact ⟨.NeedMore, hfields, rfl⟩
  | Error error => simp only [spec_ok]; exact ⟨.Error error, hfields, rfl⟩
  | Success next pair =>
    rcases pair with ⟨value, empty⟩
    cases empty
    change (ok (.Success next value) : Result (ParseOutcome U64))
      ⦃ result => Partial.markerOutcome input cursor status result ⦄
    simp only [spec_ok]
    exact ⟨.Success next (value, ()), hfields, value, rfl, rfl⟩

/-- A partial body cannot succeed before EOF is confirmed, even with all payload bytes. -/
theorem record_body_partial_spec (input : Slice U8) (cursor : Cursor) (version flags : U64)
    (count : Usize) (hvalid : Spec.validCursor input cursor) (haligned : cursor.bit.val = 0) :
    parse_record_body input cursor version flags count .Partial
      ⦃ result => Partial.recordBodyOutcome input cursor count result ⦄ := by
  have hparts : cursor.bit.val < 8 ∧ cursor.byte.val ≤ input.val.length ∧
      (cursor.byte.val = input.val.length → cursor.bit.val = 0) := by
    unfold Spec.validCursor Spec.position at hvalid
    omega
  unfold parse_record_body
  step with seq_with_spec TakeAligned.Insts.RusthammerParserInputSharedInputSliceU8
    End.Insts.RusthammerParserInputTuple { first := { count }, second := () } input cursor .Partial
    (fun start => Partial.primitive .Partial (Spec.takeAlignedOutcome input start count))
    (fun start => Partial.endOutcome input start .Partial)
    (fun start => take_aligned_with_spec { count } input start .Partial)
    (fun start => end_with_spec input start .Partial) as ⟨outcome, houtcome⟩
  rcases houtcome with ⟨taken, ⟨oldTaken, htaken, rfl⟩, hrest⟩
  simp only [Spec.takeAlignedOutcome, if_pos hparts, if_pos haligned] at htaken
  by_cases hfit : cursor.byte.val + count.val ≤ input.val.length
  · simp only [if_pos hfit] at htaken
    rcases htaken with ⟨next, payload, rfl, hbyte, hbit, hpayload⟩
    simp only [Partial.primitiveResult, Spec.completedResult] at hrest
    rcases hrest with ⟨ended, ⟨oldEnded, hended, rfl⟩, hrest⟩
    have hnext : Spec.validCursor input next := by
      simp only [Spec.validCursor, Spec.position, hbyte, hbit, UScalar.ofNatCore_val_eq]
      omega
    simp only [Spec.endOutcome, if_pos hnext] at hended
    by_cases hexact : cursor.byte.val + count.val = input.val.length
    · have hend : Spec.position next = 8 * input.val.length := by
        simp only [Spec.position, hbyte, hbit, UScalar.ofNatCore_val_eq]
        omega
      simp only [if_pos hend] at hended
      cases hended
      simp only [Partial.endResult] at hrest
      cases hrest
      have hnotTrailing : ¬cursor.byte.val + count.val < input.val.length := by omega
      simp only [spec_ok, Partial.recordBodyOutcome, if_neg hnotTrailing]
    · have hnotend : ¬Spec.position next = 8 * input.val.length := by
        simp only [Spec.position, hbyte, hbit, UScalar.ofNatCore_val_eq]
        omega
      simp only [if_neg hnotend] at hended
      cases hended
      simp only [Partial.endResult] at hrest
      cases hrest
      have htrailing : cursor.byte.val + count.val < input.val.length := by omega
      simp only [spec_ok, Partial.recordBodyOutcome, if_pos htrailing]
  · simp only [if_neg hfit] at htaken
    cases htaken
    simp only [Partial.primitiveResult] at hrest
    cases hrest
    have hnotTrailing : ¬cursor.byte.val + count.val < input.val.length := by omega
    simp only [spec_ok, Partial.recordBodyOutcome, if_neg hnotTrailing]


/-- Exact partial-input behavior for all raw cursors and byte buffers. -/
theorem record_partial_spec (parser : RecordParser) (input : Slice U8) (cursor : Cursor)
    (hconfig : Spec.validRecordParser parser) :
    RecordParser.Insts.RusthammerParserInputRecord.parse_with parser input cursor .Partial
      ⦃ result => Partial.recordOutcome input cursor result ⦄ := by
  change parser = Spec.recordParser at hconfig
  subst parser
  unfold RecordParser.Insts.RusthammerParserInputRecord.parse_with
  step with take_aligned_with_spec { count := 0#usize } input cursor .Partial
    as ⟨checkedOutcome, hcheckedOutcome⟩
  rcases hcheckedOutcome with ⟨checked, hchecked, rfl⟩
  have hparts : (cursor.bit.val < 8 ∧ cursor.byte.val ≤ input.val.length ∧
      (cursor.byte.val = input.val.length → cursor.bit.val = 0)) ↔
      Spec.validCursor input cursor := by
    unfold Spec.validCursor Spec.position
    omega
  simp only [Spec.takeAlignedOutcome, hparts] at hchecked
  by_cases hvalid : Spec.validCursor input cursor
  · simp only [if_pos hvalid] at hchecked
    by_cases haligned : cursor.bit.val = 0
    · have hbyte : cursor.byte.val ≤ input.val.length := by
        unfold Spec.validCursor Spec.position at hvalid
        omega
      simp only [if_pos haligned, UScalar.ofNatCore_val_eq, Nat.add_zero, if_pos hbyte] at hchecked
      rcases hchecked with ⟨checkedNext, empty, rfl, _, _, _⟩
      simp only [Partial.primitiveResult, Spec.completedResult]
      step with verify_with_spec fieldsInst predicateInst { parser := fieldsParser, predicate := () }
        input cursor .Partial
        (fun start => Partial.primitive .Partial (Spec.recordHeaderOutcome input start))
        Spec.recordHeaderAllowed (record_header_with_spec input cursor .Partial hvalid haligned)
        (fun _ fields _ => record_predicate_spec fields) as ⟨header, hheader⟩
      rcases hheader with ⟨rawOutcome, ⟨raw, hraw, rfl⟩, hheader⟩
      by_cases hheaderFit : cursor.byte.val + 3 ≤ input.val.length
      · simp only [Spec.recordHeaderOutcome, if_pos hheaderFit] at hraw
        rcases hraw with ⟨next, version, flags, length, rfl, hnext, hnextByte, hnextBit,
          hversion, hflags, hlength⟩
        simp only [Partial.primitiveResult, Spec.completedResult] at hheader
        by_cases hallowed : Spec.recordHeaderAllowed (version, (flags, length))
        · simp only [if_pos hallowed] at hheader
          cases hheader
          have hlengthBound : length.val ≤ 1024 := hallowed.2
          have hformat : Spec.recordVersion input cursor = 1 ∧
              Spec.recordLength input cursor ≤ 1024 := by
            exact ⟨hversion.symm.trans hallowed.1, by omega⟩
          dsimp only
          step with UScalar.cast_inBounds_spec .Usize length (by scalar_tac) as ⟨count, hcount⟩
          step with record_body_partial_spec input next version flags count hnext hnextBit
            as ⟨result, hresult⟩
          simpa only [Partial.recordOutcome, if_pos hvalid, if_pos haligned, if_pos hheaderFit,
            if_pos hformat, Partial.recordBodyOutcome, hnextByte, hcount, hlength] using hresult
        · simp only [if_neg hallowed] at hheader
          cases hheader
          have hformat : ¬(Spec.recordVersion input cursor = 1 ∧
              Spec.recordLength input cursor ≤ 1024) := by
            simpa only [Spec.recordHeaderAllowed, hversion, hlength] using hallowed
          simp only [spec_ok, Partial.recordOutcome, if_pos hvalid, if_pos haligned,
            if_pos hheaderFit, if_neg hformat]
      · simp only [Spec.recordHeaderOutcome, if_neg hheaderFit] at hraw
        cases hraw
        simp only [Partial.primitiveResult] at hheader
        cases hheader
        simp only [spec_ok, Partial.recordOutcome, if_pos hvalid, if_pos haligned, if_neg hheaderFit]
    · simp only [if_neg haligned] at hchecked
      cases hchecked
      simp only [Partial.primitiveResult, Spec.completedResult, spec_ok,
        Partial.recordOutcome, if_pos hvalid, if_neg haligned]
  · simp only [if_neg hvalid] at hchecked
    cases hchecked
    simp only [Partial.primitiveResult, Spec.completedResult, spec_ok,
      Partial.recordOutcome, if_neg hvalid]

end RustHammer.Proofs
