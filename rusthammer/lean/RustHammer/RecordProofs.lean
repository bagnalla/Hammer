import RustHammer.ControlProofs
import RustHammer.RecordSpec

open Aeneas Aeneas.Std Result WP

namespace RustHammer.Proofs
open Code
open record_example

theorem record_new_spec :
    RecordParser.new ⦃ result => result = .Ok Spec.recordParser ⦄ := by
  unfold RecordParser.new
  step with bits_new_spec 3#u8 as ⟨version, hv⟩
  simp [Spec.bitsNewOutcome] at hv
  simp only [hv]
  step with bits_new_spec 5#u8 as ⟨flags, hf⟩
  simp [Spec.bitsNewOutcome] at hf
  simp only [hf]
  step with bits_new_spec 16#u8 as ⟨length, hl⟩
  simp [Spec.bitsNewOutcome] at hl
  simp [hl, Spec.recordParser, spec_ok]

theorem record_new_valid (parser : RecordParser)
    (hnew : RecordParser.new = ok (.Ok parser)) : Spec.validRecordParser parser := by
  have hspec := record_new_spec
  rw [hnew] at hspec
  simpa only [spec_ok, core.result.Result.Ok.injEq] using hspec

private abbrev fieldsParser : Seq Bits (Seq Bits Bits) :=
  { first := Spec.recordParser.version,
    second := { first := Spec.recordParser.flags, second := Spec.recordParser.length } }

private abbrev fieldsInst := Seq.Insts.RusthammerParserInputPair
  Bits.Insts.RusthammerParserInputU64
  (Seq.Insts.RusthammerParserInputPair
    Bits.Insts.RusthammerParserInputU64 Bits.Insts.RusthammerParserInputU64)

private abbrev predicateInst :=
  ParserInputRecordParserRecord.parse_with.closure.Insts.CoreOpsFunctionFnTupleShared0PairU64PairU64U64Bool

/-- Relational sequencing of three numeric fields gives the header's fixed byte layout. -/
theorem record_fields_decode (input : Slice U8) (cursor : Cursor)
    (result : Spec.ParseResult Spec.HeaderFields)
    (hvalid : Spec.validCursor input cursor) (haligned : cursor.bit.val = 0)
    (hfields : Spec.sequence (fun start => Spec.bitsOutcome input start 3#u8)
      (Spec.sequence (fun start => Spec.bitsOutcome input start 5#u8)
        (fun start => Spec.bitsOutcome input start 16#u8)) cursor result) :
    Spec.recordHeaderOutcome input cursor result := by
  rcases hfields with ⟨vresult, hv, hrest⟩
  simp only [Spec.bitsOutcome, if_pos hvalid, UScalar.ofNatCore_val_eq] at hv
  by_cases hvfit : Spec.position cursor + 3 ≤ 8 * input.val.length
  · simp only [if_pos hvfit] at hv
    rcases hv with ⟨c1, version, rfl, hc1, hpos1, hversion⟩
    simp only [UScalar.ofNatCore_val_eq] at hpos1 hversion
    rcases hrest with ⟨rest, hf, hrest⟩
    rcases hf with ⟨fresult, hf, hlater⟩
    have hffit : Spec.position c1 + 5 ≤ 8 * input.val.length := by
      unfold Spec.position at hvfit hpos1 ⊢
      omega
    simp only [Spec.bitsOutcome, if_pos hc1, UScalar.ofNatCore_val_eq, if_pos hffit] at hf
    rcases hf with ⟨c2, flags, rfl, hc2, hpos2, hflags⟩
    simp only [UScalar.ofNatCore_val_eq] at hpos2 hflags
    rcases hlater with ⟨lresult, hl, hlater⟩
    have hpos2' : Spec.position c2 = Spec.position cursor + 8 := by omega
    by_cases hfit : cursor.byte.val + 3 ≤ input.val.length
    · have hlfit : Spec.position c2 + 16 ≤ 8 * input.val.length := by
        unfold Spec.position at hpos2' ⊢
        omega
      simp only [Spec.bitsOutcome, if_pos hc2, UScalar.ofNatCore_val_eq, if_pos hlfit] at hl
      rcases hl with ⟨c3, length, rfl, hc3, hpos3, hlength⟩
      simp only [UScalar.ofNatCore_val_eq] at hpos3 hlength
      cases hlater
      cases hrest
      simp only [Spec.recordHeaderOutcome, if_pos hfit, Spec.recordHeaderSuccess]
      refine ⟨c3, version, flags, length, rfl, hc3, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [Spec.validCursor, Spec.position] at hc3 hpos2' hpos3
        omega
      · simp only [Spec.validCursor, Spec.position] at hc3 hpos2' hpos3
        omega
      · simpa only [Spec.recordVersion] using hversion
      · simpa only [Spec.recordFlags, hpos1] using hflags
      · simpa only [Spec.recordLength, hpos2'] using hlength
    · have hlshort : ¬Spec.position c2 + 16 ≤ 8 * input.val.length := by
        unfold Spec.position at hpos2' ⊢
        omega
      simp only [Spec.bitsOutcome, if_pos hc2, UScalar.ofNatCore_val_eq, if_neg hlshort] at hl
      cases hl
      cases hlater
      simpa only [Spec.recordHeaderOutcome, if_neg hfit] using hrest
  · have hshort : ¬cursor.byte.val + 3 ≤ input.val.length := by
      unfold Spec.position at hvfit
      omega
    simp only [if_neg hvfit] at hv
    cases hv
    simpa only [Spec.recordHeaderOutcome, if_neg hshort] using hrest

theorem record_header_fields_spec (input : Slice U8) (cursor : Cursor)
    (hvalid : Spec.validCursor input cursor) (haligned : cursor.bit.val = 0) :
    fieldsInst.parse_with fieldsParser input cursor ParseContext.FINAL
      ⦃ result => Spec.completed (Spec.recordHeaderOutcome input cursor) result ⦄ := by
  let bi := Bits.Insts.RusthammerParserInputU64
  have hv (start : Cursor) := bits_spec Spec.recordParser.version input start (by decide)
  have hf (start : Cursor) := bits_spec Spec.recordParser.flags input start (by decide)
  have hl (start : Cursor) := bits_spec Spec.recordParser.length input start (by decide)
  have htail (start : Cursor) := seq_spec bi bi fieldsParser.second input start
    (fun start => Spec.bitsOutcome input start 5#u8)
    (fun start => Spec.bitsOutcome input start 16#u8) hf hl
  change Seq.Insts.RusthammerParserInputPair.parse_with bi
    (Seq.Insts.RusthammerParserInputPair bi bi) fieldsParser input cursor ParseContext.FINAL
    ⦃ result => Spec.completed (Spec.recordHeaderOutcome input cursor) result ⦄
  step with seq_spec bi (Seq.Insts.RusthammerParserInputPair bi bi) fieldsParser input cursor
    (fun start => Spec.bitsOutcome input start 3#u8)
    (Spec.sequence (fun start => Spec.bitsOutcome input start 5#u8)
      (fun start => Spec.bitsOutcome input start 16#u8)) hv htail as ⟨outcome, houtcome⟩
  rcases houtcome with ⟨result, hresult, rfl⟩
  simp only [Spec.completed_embed]
  exact record_fields_decode input cursor result hvalid haligned hresult

theorem record_predicate_spec (fields : Spec.HeaderFields) :
    predicateInst.call () fields ⦃ result => result = decide (Spec.recordHeaderAllowed fields) ⦄ := by
  rcases fields with ⟨version, flags, length⟩
  change record_header.closure.Insts.CoreOpsFunctionFnTupleShared0PairU64PairU64U64Bool.call ()
    (version, flags, length) ⦃ result => result = decide (Spec.recordHeaderAllowed (version, flags, length)) ⦄
  simp only [record_header.closure.Insts.CoreOpsFunctionFnTupleShared0PairU64PairU64U64Bool.call,
    MAX_RECORD_PAYLOAD]
  by_cases hversion : version = 1#u64
  · simp [hversion, Spec.recordHeaderAllowed, spec_ok]
  · have hv : version.val ≠ 1 := by scalar_tac
    simp [hversion, Spec.recordHeaderAllowed, hv, spec_ok]

/-- The private payload helper has no configuration assumption on the requested count. -/
theorem record_body_spec (input : Slice U8) (cursor : Cursor) (version flags : U64) (count : Usize)
    (hvalid : Spec.validCursor input cursor) (haligned : cursor.bit.val = 0) :
    DirectRun.record_example.parse_record_body input cursor version flags count ParseContext.FINAL
      ⦃ result => Spec.completed (Spec.recordBodyOutcome input cursor version flags count) result ⦄ := by
  have hparts : cursor.bit.val < 8 ∧ cursor.byte.val ≤ input.val.length ∧
      (cursor.byte.val = input.val.length → cursor.bit.val = 0) := by
    unfold Spec.validCursor Spec.position at hvalid
    omega
  rw [DirectRun.record_example.parse_record_body_eq]
  step with seq_spec TakeAligned.Insts.RusthammerParserInputSharedInputSliceU8
    End.Insts.RusthammerParserInputTuple { first := { count }, second := () } input cursor
    (fun start => Spec.takeAlignedOutcome input start count) (Spec.endOutcome input)
    (fun start => take_aligned_parser_spec { count } input start) (end_spec input)
    as ⟨outcome, houtcome⟩
  rcases houtcome with ⟨fields, hfields, rfl⟩
  rcases hfields with ⟨taken, htaken, hrest⟩
  simp only [Spec.takeAlignedOutcome, if_pos hparts, if_pos haligned] at htaken
  by_cases hfit : cursor.byte.val + count.val ≤ input.val.length
  · simp only [if_pos hfit] at htaken
    rcases htaken with ⟨next, payload, rfl, hbyte, hbit, hpayload⟩
    rcases hrest with ⟨ended, hended, hrest⟩
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
      cases hrest
      change (ok (.Success next { version, flags, payload }) : Result (ParseOutcome Record))
        ⦃ result => Spec.completed (Spec.recordBodyOutcome input cursor version flags count) result ⦄
      simp only [spec_ok, Spec.completed_success]
      simp only [Spec.recordBodyOutcome, if_pos hfit, if_pos hexact,
        Spec.recordBodySuccess]
      exact ⟨next, { version, flags, payload }, rfl, by omega, by simp [hbit], rfl, rfl, hpayload⟩
    · have hnotend : ¬Spec.position next = 8 * input.val.length := by
        simp only [Spec.position, hbyte, hbit, UScalar.ofNatCore_val_eq]
        omega
      simp only [if_neg hnotend] at hended
      cases hended
      cases hrest
      simp [Spec.completedResult,Spec.recordBodyOutcome, hfit, hexact, spec_ok]
  · simp only [if_neg hfit] at htaken
    cases htaken
    cases hrest
    simp [Spec.completedResult,Spec.recordBodyOutcome, hfit, spec_ok]

/-- The complete parser satisfies the format contract for all inputs and raw cursors. -/
theorem record_parser_spec (parser : RecordParser) (input : Slice U8) (cursor : Cursor)
    (hconfig : Spec.validRecordParser parser) :
    RecordParser.Insts.RusthammerParserInputRecord.parse_with parser input cursor ParseContext.FINAL
      ⦃ result => Spec.completed (Spec.recordOutcome input cursor) result ⦄ := by
  change parser = Spec.recordParser at hconfig
  subst parser
  rw [RecordParser.Insts.RusthammerParserInputRecord.parse_with_eq]
  step with take_aligned_parser_spec { count := 0#usize } input cursor as ⟨checkedOutcome, hcheckedOutcome⟩
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
      simp only [Spec.completedResult]
      step with verify_spec fieldsInst predicateInst { parser := fieldsParser, predicate := () }
        input cursor (Spec.recordHeaderOutcome input) Spec.recordHeaderAllowed
        (record_header_fields_spec input cursor hvalid haligned)
        (fun _ fields _ => record_predicate_spec fields) as ⟨headerOutcome, hheaderOutcome⟩
      rcases hheaderOutcome with ⟨header, hheader, rfl⟩
      rcases hheader with ⟨raw, hraw, hheader⟩
      by_cases hheaderFit : cursor.byte.val + 3 ≤ input.val.length
      · simp only [Spec.recordHeaderOutcome, if_pos hheaderFit] at hraw
        rcases hraw with ⟨next, version, flags, length, rfl, hnext, hnextByte, hnextBit,
          hversion, hflags, hlength⟩
        by_cases hallowed : Spec.recordHeaderAllowed (version, (flags, length))
        · simp only [if_pos hallowed] at hheader
          cases hheader
          have hlengthBound : length.val ≤ 1024 := hallowed.2
          have hformat : Spec.recordVersion input cursor = 1 ∧
              Spec.recordLength input cursor ≤ 1024 := by
            exact ⟨hversion.symm.trans hallowed.1, by omega⟩
          dsimp only [Spec.completedResult]
          step with UScalar.cast_inBounds_spec .Usize length (by scalar_tac) as ⟨count, hcount⟩
          step with record_body_spec input next version flags count hnext hnextBit as ⟨outcome, houtcome⟩
          rcases houtcome with ⟨result, hresult, rfl⟩
          simp only [Spec.completed_embed]
          simp only [Spec.recordOutcome, if_pos hvalid, if_pos haligned, if_pos hheaderFit,
            if_pos hformat]
          simp only [Spec.recordBodyOutcome, hnextByte, hcount, hlength] at hresult
          by_cases hfit : cursor.byte.val + 3 + Spec.recordLength input cursor ≤ input.val.length
          · simp only [if_pos hfit] at hresult ⊢
            by_cases hexact : cursor.byte.val + 3 + Spec.recordLength input cursor = input.val.length
            · simp only [if_pos hexact] at hresult ⊢
              rcases hresult with ⟨last, record, hr, hend, hbit, hv, hf, hpayload⟩
              refine ⟨last, record, hr, hend, hbit, ?_, ?_, ?_⟩
              · simpa only [hv] using hversion
              · simpa only [hf] using hflags
              · simpa only [hnextByte, hcount, hlength] using hpayload
            · simpa only [if_neg hexact] using hresult
          · simpa only [if_neg hfit] using hresult
        · simp only [if_neg hallowed] at hheader
          cases hheader
          have hformat : ¬(Spec.recordVersion input cursor = 1 ∧
              Spec.recordLength input cursor ≤ 1024) := by
            simpa only [Spec.recordHeaderAllowed, hversion, hlength] using hallowed
          simp only [Spec.completedResult, spec_ok, Spec.completed_error]
          simp only [Spec.recordOutcome, if_pos hvalid, if_pos haligned, if_pos hheaderFit, if_neg hformat]
      · simp only [Spec.recordHeaderOutcome, if_neg hheaderFit] at hraw
        cases hraw
        cases hheader
        simp only [Spec.completedResult, spec_ok, Spec.completed_error]
        simp only [Spec.recordOutcome, if_pos hvalid, if_pos haligned, if_neg hheaderFit]
    · simp only [if_neg haligned] at hchecked
      cases hchecked
      simp only [Spec.completedResult, spec_ok, Spec.completed_error]
      simp only [Spec.recordOutcome, if_pos hvalid, if_neg haligned]
  · simp only [if_neg hvalid] at hchecked
    cases hchecked
    simp [Spec.completedResult, spec_ok, Spec.recordOutcome, hvalid]

theorem record_spec (input : Slice U8) (cursor : Cursor) (parser : RecordParser)
    (hconfig : Spec.validRecordParser parser) :
    parse_record input cursor parser ⦃ result => Spec.recordOutcome input cursor result ⦄ := by
  exact complete_spec RecordParser.Insts.RusthammerParserInputRecord parser input cursor
    (Spec.recordOutcome input cursor) (record_parser_spec parser input cursor hconfig)

/-- Every aligned record satisfying the format's version, bound, and exact length is accepted. -/
theorem record_success (input : Slice U8) (cursor : Cursor) (parser : RecordParser)
    (hconfig : Spec.validRecordParser parser) (hvalid : Spec.validCursor input cursor)
    (haligned : cursor.bit.val = 0) (hversion : Spec.recordVersion input cursor = 1)
    (hbound : Spec.recordLength input cursor ≤ 1024)
    (hexact : cursor.byte.val + 3 + Spec.recordLength input cursor = input.val.length) :
    parse_record input cursor parser ⦃ result => Spec.recordSuccess input cursor result ⦄ := by
  have hheader : cursor.byte.val + 3 ≤ input.val.length := by omega
  have hfit : cursor.byte.val + 3 + Spec.recordLength input cursor ≤ input.val.length := by omega
  simpa only [Spec.recordOutcome, if_pos hvalid, if_pos haligned, if_pos hheader,
    if_pos (And.intro hversion hbound), if_pos hfit, if_pos hexact]
    using record_spec input cursor parser hconfig

/-- Successful format outcomes have the supported version, five-bit flags, and exact bounded payload. -/
theorem record_success_properties (input : Slice U8) (cursor next : Cursor) (record : Record)
    (houtcome : Spec.recordOutcome input cursor (.Ok (next, record))) :
    record.version.val = 1 ∧ record.flags.val < 32 ∧
      record.payload.val.length = Spec.recordLength input cursor ∧
      record.payload.val.length ≤ 1024 ∧ next.byte.val = input.val.length ∧ next.bit.val = 0 := by
  unfold Spec.recordOutcome at houtcome
  split_ifs at houtcome with hvalid haligned hheader hallowed hfit hexact
  rcases houtcome with ⟨last, value, heq, hend, hbit, hversion, hflags, hpayload⟩
  cases heq
  have hflagBound : record.flags.val < 32 := by
    have hbits := unsignedBits_lt_pow input (Spec.position cursor + 3) 5
    rw [hflags, Spec.recordFlags]
    exact hbits
  have hlength : record.payload.val.length = Spec.recordLength input cursor := by
    rw [hpayload, List.length_take, List.length_drop]
    exact Nat.min_eq_left (by omega)
  exact ⟨hversion.trans hallowed.1, hflagBound, hlength, by omega, hend, hbit⟩

end RustHammer.Proofs
