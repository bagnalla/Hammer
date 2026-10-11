import RustHammer.MavlinkProofs

open Aeneas Aeneas.Std Result WP
open RustHammer.Code RustHammer.Code.input_types RustHammer.Code.mavlink_example

namespace RustHammer.Mavlink
noncomputable section
open Classical

private theorem verify_success {α : Type} (child : Cursor → Spec.ParseResult α → Prop)
    (predicate : α → Prop) [DecidablePred predicate] (start next : Cursor) (value : α)
    (h : Spec.verify child predicate start (.Ok (next, value))) :
    child start (.Ok (next, value)) ∧ predicate value := by
  obtain ⟨outcome, houtcome, hrest⟩ := h
  cases outcome with
  | Err error => cases hrest
  | Ok pair =>
    rcases pair with ⟨last, result⟩
    change (if predicate result then core.result.Result.Ok (next, value) = .Ok (last, result)
      else core.result.Result.Ok (next, value) = core.result.Result.Err ParseError.Mismatch) at hrest
    by_cases hp : predicate result
    · rw [if_pos hp] at hrest
      cases hrest
      exact ⟨houtcome, hp⟩
    · rw [if_neg hp] at hrest
      cases hrest

private theorem byte_success (input : Slice U8) (ctx : ByteOrder)
    (start next : Cursor) (value : U8)
    (h : byteOutcome input ctx start (.Ok (next, value))) :
    Spec.validCursor input next ∧ Spec.position next = Spec.position start + 8 := by
  have hr := h
  unfold byteOutcome Ordering.unsignedIntegerOutcome at hr
  split at hr
  · split at hr
    · obtain ⟨last, result, heq, hv, hp, _⟩ := hr
      cases heq
      exact ⟨hv, hp⟩
    · cases hr
  · cases hr

private theorem bits_success (input : Slice U8) (ctx : ByteOrder) (width : U8)
    (start next : Cursor) (value : U64)
    (h : bitsOutcome input ctx width start (.Ok (next, value))) :
    Spec.validCursor input next ∧ Spec.position next = Spec.position start + width.val := by
  have hr := h
  unfold bitsOutcome Ordering.outcome at hr
  split at hr
  · split at hr
    · obtain ⟨last, result, heq, hv, hp, _⟩ := hr
      cases heq
      exact ⟨hv, hp⟩
    · cases hr
  · cases hr

private theorem take_success (input : Slice U8) (ctx : ByteOrder) (count : Usize)
    (start next : Cursor) (payload : Slice U8)
    (h : takeOutcome input ctx count start (.Ok (next, payload))) :
    start.bit.val = 0 ∧ next.byte.val = start.byte.val + count.val ∧ next.bit = 0#u8 ∧
      payload.val = (input.val.drop start.byte.val).take count.val := by
  have hr := h
  unfold takeOutcome Spec.takeAlignedOutcome at hr
  split at hr
  · split at hr
    · rename_i ha
      split at hr
      · obtain ⟨last, result, heq, hb, hbit, hdata⟩ := hr
        cases heq
        exact ⟨ha, hb, hbit, hdata⟩
      · cases hr
    · cases hr
  · cases hr

theorem header_success (input : Slice U8) (ctx : ByteOrder) (start next : Cursor)
    (header : Header) (h : headerOutcome input ctx start (.Ok (next, header))) :
    Spec.validCursor input next ∧ Spec.position next = Spec.position start + 72 ∧
    header.incompat_flags = 0#u8 ∧ header.system_id ≠ 0#u8 ∧ header.component_id ≠ 0#u8 := by
  obtain ⟨fields, hfields, rfl⟩ := Proofs.map_success_value _ _ _ _ _ h
  obtain ⟨third, hfirst, hrest⟩ := Proofs.sequence_success_children _ _ _ _ _ _ hfields
  obtain ⟨first, hlen, hflags⟩ := Proofs.sequence_success_children _ _ _ _ _ _ hfirst
  obtain ⟨second, hflags, hcompat⟩ := Proofs.sequence_success_children _ _ _ _ _ _ hflags
  obtain ⟨sixth, hsource, hmessage⟩ := Proofs.sequence_success_children _ _ _ _ _ _ hrest
  obtain ⟨fourth, hseq, hids⟩ := Proofs.sequence_success_children _ _ _ _ _ _ hsource
  obtain ⟨fifth, hsys, hcomp⟩ := Proofs.sequence_success_children _ _ _ _ _ _ hids
  obtain ⟨hflags, flags⟩ := verify_success _ _ _ _ _ hflags
  obtain ⟨hsys, system⟩ := verify_success _ _ _ _ _ hsys
  obtain ⟨hcomp, component⟩ := verify_success _ _ _ _ _ hcomp
  have h1 := byte_success input ctx start first _ hlen
  have h2 := byte_success input ctx first second _ hflags
  have h3 := byte_success input ctx second third _ hcompat
  have h4 := byte_success input ctx third fourth _ hseq
  have h5 := byte_success input ctx fourth fifth _ hsys
  have h6 := byte_success input ctx fifth sixth _ hcomp
  have h7 := bits_success input ctx 24#u8 sixth next _ hmessage
  exact ⟨h7.1, by scalar_tac, flags, system, component⟩

/-- Successful frames consume exactly 12 + payload length bytes. The borrowed
payload and CRC interval are exact slices of the original input. -/
theorem frame_success (input : Slice U8) (ctx : ByteOrder) (lookup : U32 → Option U8)
    (start next : Cursor) (packet : Packet)
    (h : frameOutcome input ctx lookup start (.Ok (next, packet))) :
    start.bit.val = 0 ∧ next.bit.val = 0 ∧ Spec.validCursor input next ∧
    next.byte.val = start.byte.val + 12 + packet.header.payload_length.val ∧
    packet.payload.val =
      (input.val.drop (start.byte.val + 10)).take packet.header.payload_length.val ∧
    packet.header.incompat_flags = 0#u8 ∧
    packet.header.system_id ≠ 0#u8 ∧ packet.header.component_id ≠ 0#u8 ∧
    ∃ extra, lookup packet.header.message_id = some extra ∧
      packet.checksum.bv = crc
        ((input.val.drop (start.byte.val + 1)).take (9 + packet.header.payload_length.val))
        extra := by
  have hchild := h
  obtain ⟨bodyStart, prefixValue, hprefix, hpacket⟩ :=
    Proofs.right_success_children _ _ _ _ _ hchild
  obtain ⟨magicStart, halign, hmagic⟩ :=
    Proofs.sequence_success_children _ _ _ _ _ _ hprefix
  have halign := take_success input _ 0#usize start magicStart prefixValue.1 halign
  have hmagic := byte_success input _ magicStart bodyStart _
    (verify_success _ _ _ _ _ hmagic).1
  obtain ⟨fields, hchecked, rfl⟩ := Proofs.map_success_value _ _ _ _ _ hpacket
  obtain ⟨hfields, hcrc⟩ := verify_success _ _ _ _ _ hchecked
  obtain ⟨bodyEnd, hbody, hchecksum⟩ := Proofs.sequence_success_children _ _ _ _ _ _ hfields
  obtain ⟨_, hspan, hbody⟩ := Span.capture_success input bodyStart _ bodyEnd
    fields.1.1 fields.1.2 hbody
  obtain ⟨payloadStart, header, hheader, hpayload⟩ :=
    Proofs.bind_success_children _ _ _ _ _ hbody
  have hheader := header_success input _ bodyStart payloadStart header hheader
  obtain ⟨payload, htaken, hpair⟩ := Proofs.map_success_value _ _ _ _ _ hpayload
  have hheaderEq : fields.1.1.1 = header := congrArg Prod.fst hpair
  have hpayloadEq : fields.1.1.2 = payload := congrArg Prod.snd hpair
  have htaken := take_success input _ _ payloadStart bodyEnd payload htaken
  have hcount : (UScalar.cast .Usize header.payload_length).val = header.payload_length.val := by
    scalar_tac
  obtain ⟨checksum, hbits, _⟩ := Proofs.map_success_value _ _ _ _ _ hchecksum
  have hbits := bits_success input _ 16#u8 bodyEnd next checksum hbits
  have hm : magicStart.byte.val = start.byte.val := by scalar_tac
  have hb : bodyStart.byte.val = start.byte.val + 1 ∧ bodyStart.bit.val = 0 := by
    unfold Spec.validCursor Spec.position at hmagic
    scalar_tac
  have hp : payloadStart.byte.val = start.byte.val + 10 := by
    unfold Spec.position at hheader
    scalar_tac
  have he : bodyEnd.byte.val = start.byte.val + 10 + header.payload_length.val := by
    scalar_tac
  have hn : next.byte.val = start.byte.val + 12 + header.payload_length.val ∧
      next.bit.val = 0 := by
    unfold Spec.validCursor Spec.position at hbits
    scalar_tac
  refine ⟨halign.1, hn.2, hbits.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [packetValue, hheaderEq] using hn.1
  · simpa only [packetValue, hpayloadEq, hp, hcount, hheaderEq] using htaken.2.2.2
  · simpa only [packetValue, hheaderEq] using hheader.2.2.1
  · simpa only [packetValue, hheaderEq] using hheader.2.2.2.1
  · simpa only [packetValue, hheaderEq] using hheader.2.2.2.2
  · obtain ⟨extra, hextra, _, _, hcrc⟩ := hcrc
    refine ⟨extra, hextra, ?_⟩
    rw [hspan] at hcrc
    have hlength : bodyEnd.byte.val - (start.byte.val + 1) = 9 + header.payload_length.val := by
      omega
    simpa only [packetValue, hb.1, hlength, hheaderEq] using hcrc

/-- An aligned payload longer than the remaining input is UnexpectedEnd. -/
theorem payload_truncated (header : Header) (input : Slice U8) (start : Cursor)
    (ctx : ByteOrder) (ha : start.bit.val = 0) (hv : start.byte.val ≤ input.val.length)
    (hshort : input.val.length < start.byte.val + header.payload_length.val) :
    payloadInst.parse_with ⟨header⟩ input start ctx ⦃ result => result =
      .Err .UnexpectedEnd ⦄ := by
  step with payload_spec ⟨header⟩ input start ctx as ⟨result, hr⟩
  obtain ⟨raw, hraw, hrest⟩ := hr
  have hcount : (UScalar.cast .Usize header.payload_length).val = header.payload_length.val := by
    scalar_tac
  have hbounds : start.bit.val < 8 ∧ start.byte.val ≤ input.val.length ∧
      (start.byte.val = input.val.length → start.bit.val = 0) := by omega
  simp only [takeOutcome, Spec.takeAlignedOutcome, if_pos hbounds, if_pos ha, hcount,
    if_neg (Nat.not_le_of_lt hshort)] at hraw
  subst raw
  simp_all only []

end
end RustHammer.Mavlink
