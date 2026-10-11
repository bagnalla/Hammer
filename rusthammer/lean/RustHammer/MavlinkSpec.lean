import RustHammer.MavlinkCrcSpec
import RustHammer.OrderParserSpec
import RustHammer.BindSpec
import RustHammer.SelectionSpec
import RustHammer.SpanSpec
import RustHammer.OrderScopeProofs

open Aeneas Aeneas.Std
open RustHammer.Code.input_types RustHammer.Code.mavlink_example
open RustHammer.Code.span_types

namespace RustHammer.Mavlink
noncomputable section
open Classical

def wireOrder : Order := ⟨.HighFirst, .Little⟩

abbrev HeaderValues := (U8 × (U8 × U8)) × ((U8 × (U8 × U8)) × U64)
abbrev CheckedFields := ((Header × Slice U8) × BitSpan) × U16

/-- Numeric decoding uses the existing mathematical bit-position specification. -/
def byteOutcome (input : Slice U8) (ctx : ParseContext) (start : Cursor) :=
  Partial.primitive ctx.status (Ordering.unsignedIntegerOutcome .U8 input start ctx.order)

def bitsOutcome (input : Slice U8) (ctx : ParseContext) (width : U8) (start : Cursor) :=
  Partial.primitive ctx.status (Ordering.outcome input start width ctx.order)

def takeOutcome (input : Slice U8) (ctx : ParseContext) (count : Usize) (start : Cursor) :=
  Partial.primitive ctx.status (Spec.takeAlignedOutcome input start count)

/-- The six one-byte fields precede the 24-bit message ID. Constraints are checked
at their wire positions, before any later field is read. -/
def headerFields (input : Slice U8) (ctx : ParseContext) :=
  Partial.sequence
    (Partial.sequence (byteOutcome input ctx)
      (Partial.sequence (Partial.verify (byteOutcome input ctx) (· = 0#u8))
        (byteOutcome input ctx)))
    (Partial.sequence
      (Partial.sequence (byteOutcome input ctx)
        (Partial.sequence (Partial.verify (byteOutcome input ctx) (· ≠ 0#u8))
          (Partial.verify (byteOutcome input ctx) (· ≠ 0#u8))))
      (bitsOutcome input ctx 24#u8))

def headerValue (fields : HeaderValues) : Header :=
  { payload_length := fields.1.1, incompat_flags := fields.1.2.1,
    compat_flags := fields.1.2.2, sequence := fields.2.1.1,
    system_id := fields.2.1.2.1, component_id := fields.2.1.2.2,
    message_id := ⟨fields.2.2.bv.setWidth 32⟩ }

def headerOutcome (input : Slice U8) (ctx : ParseContext) :=
  Partial.map (headerFields input ctx) (fun fields result => result = headerValue fields)

def payloadOutcome (input : Slice U8) (ctx : ParseContext) (header : Header) :=
  Partial.map (takeOutcome input ctx (UScalar.cast .Usize header.payload_length))
    (fun payload result => result = (header, payload))

def bodyOutcome (input : Slice U8) (ctx : ParseContext) :=
  Partial.bind (headerOutcome input ctx) (payloadOutcome input ctx)

def capturedBody (input : Slice U8) (ctx : ParseContext) (start : Cursor)
    (result : ParseOutcome ((Header × Slice U8) × BitSpan)) : Prop :=
  Span.capture input start ctx.order.bit ()
    (fun pair => bodyOutcome input ctx start pair.1) (result, ())

def checksumOutcome (input : Slice U8) (ctx : ParseContext) :=
  Partial.map (bitsOutcome input ctx 16#u8)
    (fun value result => result = (⟨value.bv.setWidth 16⟩ : U16))

/-- The dialect supplies CRC_EXTRA. The checksum covers the exact transmitted
header/payload interval captured after magic and before the checksum field. -/
def checksumValid (lookup : U32 → Option U8) (fields : CheckedFields) : Prop :=
  let span := fields.1.2
  ∃ extra, lookup fields.1.1.1.message_id = some extra ∧
    span.start.bit.val = 0 ∧ span.end.bit.val = 0 ∧
    fields.2.bv = crc
      ((span.input.val.drop span.start.byte.val).take (span.end.byte.val - span.start.byte.val))
      extra

def checkedOutcome (input : Slice U8) (ctx : ParseContext) (lookup : U32 → Option U8) :=
  Partial.verify (Partial.sequence (capturedBody input ctx) (checksumOutcome input ctx))
    (checksumValid lookup)

def packetValue (fields : CheckedFields) : Packet :=
  { header := fields.1.1.1, payload := fields.1.1.2, checksum := fields.2 }

def packetOutcome (input : Slice U8) (ctx : ParseContext) (lookup : U32 → Option U8) :=
  Partial.map (checkedOutcome input ctx lookup) (fun fields result => result = packetValue fields)

/-- One frame starts aligned, has marker 0xfd, and ends just after its checksum.
This relation specifies all success, error, and incomplete-input outcomes; it
does not require EOF, decode message fields, or accept signed frames. -/
def frameOutcome (input : Slice U8) (ctx : ParseContext) (lookup : U32 → Option U8)
    (start : Cursor) : ParseOutcome Packet → Prop :=
  let wire := { ctx with order := wireOrder }
  Ordering.scope input.len (decide (wireOrder.bit ≠ ctx.order.bit)) start
    (Partial.right
      (Partial.sequence (takeOutcome input wire 0#usize)
        (Partial.verify (byteOutcome input wire) (· = 253#u8)))
      (packetOutcome input wire lookup) start)

end
end RustHammer.Mavlink
