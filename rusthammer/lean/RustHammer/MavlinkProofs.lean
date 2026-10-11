import RustHammer.MavlinkSpec
import RustHammer.MavlinkCrcProofs
import RustHammer.OrderParserProofs
import RustHammer.BindProofs
import RustHammer.SelectionProofs
import RustHammer.SpanProofs
import RustHammer.ConstructorProofs

open Aeneas Aeneas.Std Result WP
open RustHammer.Code RustHammer.Code.input_types RustHammer.Code.parser_traits
open RustHammer.Code.grammar.bytes RustHammer.Code.grammar.numeric
open RustHammer.Code.grammar.sequence RustHammer.Code.grammar.transform
open RustHammer.Code.grammar.span RustHammer.Code.grammar.order
open RustHammer.Code.mavlink_example
open header.closure.Insts checksum_predicate.closure.Insts

namespace RustHammer.Mavlink
noncomputable section
open Classical

abbrev HeaderParser := Map
  (grammar.sequence.Seq
    (grammar.sequence.Seq grammar.numeric.Byte (grammar.sequence.Seq ByteIn grammar.numeric.Byte))
    (grammar.sequence.Seq
      (grammar.sequence.Seq grammar.numeric.Byte (grammar.sequence.Seq ByteNotIn ByteNotIn)) Bits))
  header.closure

abbrev byteInst := Byte.Insts.RusthammerParser_traitsParserInputU8
abbrev inInst := ByteIn.Insts.RusthammerParser_traitsParserInputU8
abbrev notInInst := ByteNotIn.Insts.RusthammerParser_traitsParserInputU8
abbrev bitsInst := Bits.Insts.RusthammerParser_traitsParserInputU64
abbrev headerMapInst :=
  header.closure.Insts.CoreOpsFunctionFnTuplePairPairU8PairU8U8PairPairU8PairU8U8U64Header

abbrev headerFieldsInst := Seq.Insts.RusthammerParser_traitsParserInputPair
  (Seq.Insts.RusthammerParser_traitsParserInputPair byteInst
    (Seq.Insts.RusthammerParser_traitsParserInputPair inInst byteInst))
  (Seq.Insts.RusthammerParser_traitsParserInputPair
    (Seq.Insts.RusthammerParser_traitsParserInputPair byteInst
      (Seq.Insts.RusthammerParser_traitsParserInputPair notInInst notInInst)) bitsInst)

abbrev headerInst : parser_traits.Parser HeaderParser Header :=
  Map.Insts.RusthammerParser_traitsParser headerFieldsInst headerMapInst

def headerConfig (parser : HeaderParser) : Prop :=
  Spec.bitmapRepresents parser.parser.first.second.first.set [0#u8] ∧
  Spec.bitmapRepresents parser.parser.second.first.second.first.set [0#u8] ∧
  Spec.bitmapRepresents parser.parser.second.first.second.second.set [0#u8] ∧
  parser.parser.second.second.width = 24#u8

theorem byte_spec (input : Slice U8) (cursor : Cursor) (ctx : ByteOrder) :
    byteInst.parse_with () input cursor ctx ⦃ result => byteOutcome input ctx cursor result ⦄ :=
  Ordering.byte_with_spec input cursor ctx

theorem in_spec (parser : ByteIn) (expected : U8)
    (hrep : Spec.bitmapRepresents parser.set [expected])
    (input : Slice U8) (cursor : Cursor) (ctx : ByteOrder) :
    inInst.parse_with parser input cursor ctx
      ⦃ result => Contracts.verify (byteOutcome input ctx) (· = expected) cursor result ⦄ := by
  have hp : Spec.bitmapPredicate parser.set false = (· = expected) := by
    funext value
    apply propext
    simp [Spec.bitmapPredicate, hrep value]
  change ByteIn.Insts.RusthammerParser_traitsParserInputU8.parse_with parser input cursor ctx ⦃ result => _ ⦄
  step with Ordering.byte_in_with_spec parser input cursor ctx as ⟨outcome, houtcome⟩
  unfold byteOutcome
  simpa only [hp] using houtcome

theorem nonzero_spec (parser : ByteNotIn) (hrep : Spec.bitmapRepresents parser.set [0#u8])
    (input : Slice U8) (cursor : Cursor) (ctx : ByteOrder) :
    notInInst.parse_with parser input cursor ctx
      ⦃ result => Contracts.verify (byteOutcome input ctx) (· ≠ 0#u8) cursor result ⦄ := by
  have hp : Spec.bitmapPredicate parser.set true = (· ≠ 0#u8) := by
    funext value
    apply propext
    simp [Spec.bitmapPredicate, hrep value]
  change ByteNotIn.Insts.RusthammerParser_traitsParserInputU8.parse_with parser input cursor ctx
    ⦃ result => _ ⦄
  step with Ordering.byte_not_in_with_spec parser input cursor ctx as ⟨outcome, houtcome⟩
  unfold byteOutcome
  simpa only [hp] using houtcome

theorem header_fields_spec (parser : HeaderParser) (hp : headerConfig parser)
    (input : Slice U8) (cursor : Cursor) (ctx : ByteOrder) :
    headerFieldsInst.parse_with parser.parser input cursor ctx
      ⦃ result => headerFields input ctx cursor result ⦄ := by
  apply Proofs.seq_with_spec
  · intro start
    apply Proofs.seq_with_spec
    · intro start; exact byte_spec input start ctx
    · intro start
      apply Proofs.seq_with_spec
      · intro start; exact in_spec _ _ hp.1 input start ctx
      · intro start; exact byte_spec input start ctx
  · intro start
    apply Proofs.seq_with_spec
    · intro start
      apply Proofs.seq_with_spec
      · intro start; exact byte_spec input start ctx
      · intro start
        apply Proofs.seq_with_spec
        · intro start; exact nonzero_spec _ hp.2.1 input start ctx
        · intro start; exact nonzero_spec _ hp.2.2.1 input start ctx
    · intro start
      change Bits.Insts.RusthammerParser_traitsParserInputU64.parse_with
        parser.parser.second.second input start ctx ⦃ result => _ ⦄
      step with Ordering.bits_with_spec parser.parser.second.second input start ctx (by
        simp [Spec.validBits, hp.2.2.2]) as ⟨outcome, houtcome⟩
      simpa only [bitsOutcome, hp.2.2.2] using houtcome

theorem header_map_spec (fields : HeaderValues) :
    headerMapInst.call () fields ⦃ result => result = headerValue fields ⦄ := by
  rcases fields with ⟨⟨length, flags, compat⟩, ⟨⟨sequence, system, component⟩, message⟩⟩
  simp [CoreOpsFunctionFnTuplePairPairU8PairU8U8PairPairU8PairU8U8U64Header.call,
    spec_ok, headerValue, lift, bind_ok]
  apply U32.bv_eq_imp_eq
  rfl

theorem header_spec (parser : HeaderParser) (hp : headerConfig parser)
    (input : Slice U8) (cursor : Cursor) (ctx : ByteOrder) :
    headerInst.parse_with parser input cursor ctx
      ⦃ result => headerOutcome input ctx cursor result ⦄ := by
  apply Proofs.map_with_spec
  · exact header_fields_spec parser hp input cursor ctx
  · intro next value _
    exact header_map_spec value

theorem header_constructor : header ⦃ result => headerConfig result ⦄ := by
  unfold header
  simp only [lift, bind_ok, Code.grammar.sequence.seq]
  step with Proofs.byte_in_new_spec _ as ⟨flags, hflags⟩
  step with Proofs.byte_not_in_new_spec _ as ⟨system, hsystem⟩
  step with Proofs.byte_not_in_new_spec _ as ⟨component, hcomponent⟩
  have hbits : fixed_bits 24#u8 = ok ({ width := 24#u8 } : Bits) := by
    simp [fixed_bits, Bits.new]
  simp only [hbits, bind_ok, Code.grammar.transform.map, spec_ok]
  exact ⟨hflags, hsystem, hcomponent, rfl⟩

abbrev payloadInst : parser_traits.Parser Payload (Header × Slice U8) :=
  Payload.Insts.RusthammerParser_traitsParserInputPairHeaderSharedInputSliceU8
abbrev factoryInst := payload_factory.closure.Insts.CoreOpsFunctionFnTupleHeaderPayload
abbrev bodyInst := Bind.Insts.RusthammerParser_traitsParser headerInst factoryInst payloadInst
abbrev checksumMapInst := checksum_reader.closure.Insts.CoreOpsFunctionFnTupleU64U16
abbrev checksumInst := Map.Insts.RusthammerParser_traitsParser bitsInst checksumMapInst

theorem payload_spec (parser : Payload) (input : Slice U8) (cursor : Cursor)
    (ctx : ByteOrder) :
    payloadInst.parse_with parser input cursor ctx
      ⦃ result => payloadOutcome input ctx parser.header cursor result ⦄ := by
  unfold parser_traits.Parser.parse_with payloadInst
  simp only [Payload.Insts.RusthammerParser_traitsParserInputPairHeaderSharedInputSliceU8.parse_with,
    lift, bind_ok]
  step with Ordering.take_aligned_with_spec _ input cursor ctx as ⟨outcome, houtcome⟩
  have hcast : core.convert.num.FromUsizeU8.from parser.header.payload_length =
      UScalar.cast .Usize parser.header.payload_length := by rfl
  rw [hcast] at houtcome
  cases outcome with
  | Err error => exact ⟨.Err error, houtcome, rfl⟩
  | Ok pair =>
    rcases pair with ⟨next, value⟩
    exact ⟨.Ok (next, value), houtcome, _, rfl, rfl⟩

theorem body_spec (parser : Bind HeaderParser payload_factory.closure)
    (hp : headerConfig parser.parser) (input : Slice U8) (cursor : Cursor)
    (ctx : ByteOrder) :
    bodyInst.parse_with parser input cursor ctx
      ⦃ result => bodyOutcome input ctx cursor result ⦄ := by
  apply Proofs.bind_with_spec (constructed := fun header result => result.header = header)
  · exact header_spec parser.parser hp input cursor ctx
  · intro next value _
    simp [payload_factory.closure.Insts.CoreOpsFunctionFnTupleHeaderPayload.call, spec_ok]
  · intro next value child _ hchild
    rw [← hchild]
    exact payload_spec child input next ctx

theorem checksum_spec (parser : Map Bits checksum_reader.closure)
    (hp : parser.parser.width = 16#u8) (input : Slice U8) (cursor : Cursor)
    (ctx : ByteOrder) :
    checksumInst.parse_with parser input cursor ctx
      ⦃ result => checksumOutcome input ctx cursor result ⦄ := by
  apply Proofs.map_with_spec
  · change Bits.Insts.RusthammerParser_traitsParserInputU64.parse_with parser.parser input cursor ctx
      ⦃ result => _ ⦄
    step with Ordering.bits_with_spec parser.parser input cursor ctx (by
      simp [Spec.validBits, hp]) as ⟨outcome, houtcome⟩
    simpa only [bitsOutcome, hp] using houtcome
  · intro next value _
    simp [checksum_reader.closure.Insts.CoreOpsFunctionFnTupleU64U16.call, spec_ok]
    apply U16.bv_eq_imp_eq
    rfl

abbrev predicateInst {F : Type} (fi : core.ops.function.Fn F U32 (Option U8)) :=
  CoreOpsFunctionFnTupleShared0PairPairPairHeaderShared1SliceU8BitSpanU16Bool fi

/-- A dialect callback must terminate and implement the stated lookup. -/
def lookupContract {F : Type} (fi : core.ops.function.Fn F U32 (Option U8))
    (callback : F) (lookup : U32 → Option U8) : Prop :=
  ∀ message, fi.call callback message ⦃ result => result = lookup message ⦄

theorem checksum_predicate_spec {F : Type} (fi : core.ops.function.Fn F U32 (Option U8))
    (callback : F) (lookup : U32 → Option U8) (hf : lookupContract fi callback lookup)
    (fields : CheckedFields) (hv : Span.valid fields.1.2) :
    (predicateInst fi).call callback fields
      ⦃ result => result = decide (checksumValid lookup fields) ⦄ := by
  rcases fields with ⟨⟨⟨header, payload⟩, span⟩, checksum⟩
  unfold predicateInst
  simp only [CoreOpsFunctionFnTupleShared0PairPairPairHeaderShared1SliceU8BitSpanU16Bool.call]
  step with hf header.message_id as ⟨extra, hextra⟩
  step with Span.as_bytes_spec span hv as ⟨view, hview⟩
  cases he : lookup header.message_id with
  | none => simp [hextra, he, checksumValid, spec_ok]
  | some extra =>
    simp only [hextra, he]
    by_cases ha : span.start.bit.val = 0 ∧ span.end.bit.val = 0
    · simp only [Span.byteView, if_pos ha] at hview
      obtain ⟨bytes, rfl, hbytes⟩ := hview
      step with crc_spec bytes extra as ⟨computed, hcomputed⟩
      have heq : computed = checksum ↔ checksum.bv = crc bytes.val extra := by
        rw [← hcomputed]
        constructor
        · intro h; rw [h]
        · intro h; exact U16.bv_eq_imp_eq _ _ h.symm
      simp [checksumValid, he, ha.1, ha.2, heq, hbytes]
    · have hn : view = none := by simpa only [Span.byteView, if_neg ha] using hview
      simp only [hn, spec_ok, checksumValid, he, Option.some.injEq,
        Bool.false_eq, decide_eq_false_iff_not]
      rintro ⟨_, _, hs, he, _⟩
      exact ha ⟨hs, he⟩

abbrev BodyParser := Bind HeaderParser payload_factory.closure
abbrev FieldsParser := grammar.sequence.Seq (WithSpan BodyParser)
  (Map Bits checksum_reader.closure)
abbrev CheckedParser (F : Type) := Verify FieldsParser (checksum_predicate.closure F)
abbrev FrameParser (F : Type) := WithByteOrder
  (Right (grammar.sequence.Seq TakeAligned ByteIn) (PacketFields (CheckedParser F)))

abbrev spanInst :=
  WithSpan.Insts.RusthammerParser_traitsParserInputPairClause0_OutputBitSpan bodyInst
abbrev fieldsInst := Seq.Insts.RusthammerParser_traitsParserInputPair spanInst checksumInst
abbrev checkedInst {F : Type} (fi : core.ops.function.Fn F U32 (Option U8)) :=
  Verify.Insts.RusthammerParser_traitsParser fieldsInst (predicateInst fi)
abbrev packetInst {F : Type} (fi : core.ops.function.Fn F U32 (Option U8)) :
    parser_traits.Parser (PacketFields (CheckedParser F)) Packet :=
  PacketFields.Insts.RusthammerParser_traitsParserInputPacket (checkedInst fi)
abbrev takeInst := TakeAligned.Insts.RusthammerParser_traitsParserInputSharedInputSliceU8
abbrev prefixInst := Seq.Insts.RusthammerParser_traitsParserInputPair takeInst inInst
abbrev frameInst {F : Type} (fi : core.ops.function.Fn F U32 (Option U8)) :=
  WithByteOrder.Insts.RusthammerParser_traitsParser (Right.Insts.RusthammerParser_traitsParser prefixInst (packetInst fi))

def fieldsConfig (parser : FieldsParser) : Prop :=
  headerConfig parser.first.parser.parser ∧ parser.second.parser.width = 16#u8

def frameConfig {F : Type} (parser : FrameParser F) : Prop :=
  fieldsConfig parser.parser.second.parser.parser ∧
  parser.parser.first.first.count = 0#usize ∧
  Spec.bitmapRepresents parser.parser.first.second.set [253#u8] ∧ parser.byte_order = wireOrder

theorem fields_spec (parser : FieldsParser) (hp : fieldsConfig parser)
    (input : Slice U8) (cursor : Cursor) (ctx : ByteOrder) :
    fieldsInst.parse_with parser input cursor ctx
      ⦃ result => Contracts.sequence (capturedBody input ctx) (checksumOutcome input ctx)
        cursor result ⦄ := by
  apply Proofs.seq_with_spec
  · intro start
    apply Span.with_span_with_spec
    intro _
    exact body_spec parser.first.parser hp.1 input start ctx
  · intro start
    exact checksum_spec parser.second hp.2 input start ctx

theorem checked_spec {F : Type} (fi : core.ops.function.Fn F U32 (Option U8))
    (parser : CheckedParser F) (hp : fieldsConfig parser.parser)
    (lookup : U32 → Option U8) (hf : lookupContract fi parser.predicate lookup)
    (input : Slice U8) (cursor : Cursor) (ctx : ByteOrder) :
    (checkedInst fi).parse_with parser input cursor ctx
      ⦃ result => checkedOutcome input ctx lookup cursor result ⦄ := by
  apply Proofs.verify_with_spec
  · exact fields_spec parser.parser hp input cursor ctx
  · intro next fields hfields
    obtain ⟨middle, hbody, _⟩ := Proofs.sequence_success_children _ _ _ _ _ _ hfields
    have hspan := Span.capture_success input cursor _ middle
      fields.1.1 fields.1.2 hbody
    exact checksum_predicate_spec fi parser.predicate lookup hf fields hspan.1

theorem packet_spec {F : Type} (fi : core.ops.function.Fn F U32 (Option U8))
    (parser : PacketFields (CheckedParser F)) (hp : fieldsConfig parser.parser.parser)
    (lookup : U32 → Option U8) (hf : lookupContract fi parser.parser.predicate lookup)
    (input : Slice U8) (cursor : Cursor) (ctx : ByteOrder) :
    (packetInst fi).parse_with parser input cursor ctx
      ⦃ result => packetOutcome input ctx lookup cursor result ⦄ := by
  unfold parser_traits.Parser.parse_with packetInst
  simp only [PacketFields.Insts.RusthammerParser_traitsParserInputPacket.parse_with]
  have hc := checked_spec fi parser.parser hp lookup hf input cursor ctx
  change Verify.Insts.RusthammerParser_traitsParser.parse_with fieldsInst (predicateInst fi)
    parser.parser input cursor ctx ⦃ result => _ ⦄ at hc
  step with hc as ⟨outcome, houtcome⟩
  cases outcome with
  | Err error => exact ⟨.Err error, houtcome, rfl⟩
  | Ok pair =>
    rcases pair with ⟨next, value⟩

    rcases value with ⟨⟨⟨header, payload⟩, span⟩, checksum⟩
    simp only [uncurry_apply_pair, spec_ok]
    exact ⟨.Ok (next, (((header, payload), span), checksum)), houtcome, _, rfl, rfl⟩

theorem frame_parser_spec {F : Type} (fi : core.ops.function.Fn F U32 (Option U8))
    (parser : FrameParser F) (hp : frameConfig parser) (lookup : U32 → Option U8)
    (hf : lookupContract fi parser.parser.second.parser.predicate lookup)
    (input : Slice U8) (cursor : Cursor) (ctx : ByteOrder) :
    (frameInst fi).parse_with parser input cursor ctx
      ⦃ result => frameOutcome input ctx lookup cursor result ⦄ := by
  unfold frameOutcome
  rw [← hp.2.2.2]
  change WithByteOrder.Insts.RusthammerParser_traitsParser.parse_with
    (Right.Insts.RusthammerParser_traitsParser prefixInst (packetInst fi))
    parser input cursor ctx ⦃ result => _ ⦄
  apply Ordering.with_byte_order_spec
  apply Proofs.right_with_spec
  · intro start
    apply Proofs.seq_with_spec
    · intro first
      change TakeAligned.Insts.RusthammerParser_traitsParserInputSharedInputSliceU8.parse_with
        parser.parser.first.first input first parser.byte_order ⦃ result => _ ⦄
      step with Ordering.take_aligned_with_spec parser.parser.first.first input first
        parser.byte_order as ⟨outcome, houtcome⟩
      simpa only [takeOutcome, hp.2.1] using houtcome
    · intro first
      exact in_spec _ _ hp.2.2.1 input first _
  · intro start
    exact packet_spec fi parser.parser.second hp.1 lookup hf input start _

theorem frame_constructor {F : Type} (fi : core.ops.function.Fn F U32 (Option U8))
    (callback : F) :
    frame_grammar fi callback ⦃ result => frameConfig result ∧
      result.parser.second.parser.predicate = callback ⦄ := by
  unfold frame_grammar
  step with header_constructor as ⟨parser, hp⟩
  have hbits : fixed_bits 16#u8 = ok ({ width := 16#u8 } : Bits) := by
    simp [fixed_bits, Bits.new]
  simp only [payload_factory, Code.grammar.sequence.bind, checksum_reader, hbits,
    Code.grammar.transform.map, Code.grammar.sequence.seq, checksum_predicate,
    Code.grammar.transform.verify, lift, bind_ok]
  step with Proofs.byte_in_new_spec _ as ⟨magic, hmagic⟩
  simp only [frameConfig, fieldsConfig, hp, true_and, and_true]
  exact ⟨hmagic, rfl⟩

abbrev mavlinkInst {F : Type} (fi : core.ops.function.Fn F U32 (Option U8)) :
    parser_traits.Parser (MavlinkV2 F) Packet :=
  MavlinkV2.Insts.RusthammerParser_traitsParserAPacket fi

/-- The actual extracted example is total and meets the framing specification
for every buffer, cursor, input, and ambient order. -/
theorem mavlink_spec {F : Type} (fi : core.ops.function.Fn F U32 (Option U8))
    (parser : MavlinkV2 F) (lookup : U32 → Option U8)
    (hf : lookupContract fi parser.crc_extra lookup)
    (input : Slice U8) (cursor : Cursor) (ctx : ByteOrder) :
    (mavlinkInst fi).parse_with parser input cursor ctx
      ⦃ result => frameOutcome input ctx lookup cursor result ⦄ := by
  unfold parser_traits.Parser.parse_with mavlinkInst
  simp only [MavlinkV2.Insts.RusthammerParser_traitsParserAPacket.parse_with]
  step with frame_constructor (Shared0F.Insts.CoreOpsFunctionFn fi) parser.crc_extra
    as ⟨frame, hframe, hcallback⟩
  change (frameInst (Shared0F.Insts.CoreOpsFunctionFn fi)).parse_with frame input cursor ctx
    ⦃ result => frameOutcome input ctx lookup cursor result ⦄
  apply frame_parser_spec _ frame hframe lookup _ input cursor ctx
  rw [hcallback]
  exact hf

def heartbeatLookup (message : U32) : Option U8 :=
  if message = 0#u32 then some 50#u8 else none

theorem heartbeat_lookup_spec (message : U32) :
    heartbeat_crc_extra message ⦃ result => result = heartbeatLookup message ⦄ := by
  unfold heartbeat_crc_extra heartbeatLookup
  split <;> simp_all [spec_ok]
  all_goals
    have hz : (0#32).toNat = 0 := by decide
    simp_all only [UScalar.val, not_false_eq_true]

end
end RustHammer.Mavlink
