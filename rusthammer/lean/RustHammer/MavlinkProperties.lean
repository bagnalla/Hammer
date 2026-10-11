import RustHammer.MavlinkProofs

open Aeneas Aeneas.Std Result WP
open RustHammer.Code RustHammer.Code.input_types RustHammer.Code.mavlink_example

namespace RustHammer.Mavlink
noncomputable section
open Classical

private theorem primitive_success {α : Type} (status : InputStatus)
    (contract : Spec.ParseResult α → Prop) (next : Cursor) (value : α)
    (h : Partial.primitive status contract (.Success next value)) :
    contract (.Ok (next, value)) := by
  rcases h with ⟨parsed, hparsed, heq⟩
  cases parsed with
  | Ok pair => cases pair; cases status <;> simp_all [Partial.primitiveResult, Spec.completedResult]
  | Err error =>
    cases status <;> cases error <;> simp_all [Partial.primitiveResult, Spec.completedResult]

private theorem verify_success {α : Type} (child : Cursor → ParseOutcome α → Prop)
    (predicate : α → Prop) [DecidablePred predicate] (start next : Cursor) (value : α)
    (h : Partial.verify child predicate start (.Success next value)) :
    child start (.Success next value) ∧ predicate value := by
  obtain ⟨outcome, houtcome, hrest⟩ := h
  cases outcome with
  | NeedMore => cases hrest
  | Error error => cases hrest
  | Success last result =>
    change (if predicate result then ParseOutcome.Success next value = .Success last result
      else ParseOutcome.Success next value = ParseOutcome.Error .Mismatch) at hrest
    by_cases hp : predicate result
    · rw [if_pos hp] at hrest
      cases hrest
      exact ⟨houtcome, hp⟩
    · rw [if_neg hp] at hrest
      cases hrest

private theorem byte_success (input : Slice U8) (ctx : ParseContext)
    (start next : Cursor) (value : U8)
    (h : byteOutcome input ctx start (.Success next value)) :
    Spec.validCursor input next ∧ Spec.position next = Spec.position start + 8 := by
  have hr := primitive_success ctx.status _ next value h
  unfold Ordering.unsignedIntegerOutcome at hr
  split at hr
  · split at hr
    · obtain ⟨last, result, heq, hv, hp, _⟩ := hr
      cases heq
      exact ⟨hv, hp⟩
    · cases hr
  · cases hr

private theorem bits_success (input : Slice U8) (ctx : ParseContext) (width : U8)
    (start next : Cursor) (value : U64)
    (h : bitsOutcome input ctx width start (.Success next value)) :
    Spec.validCursor input next ∧ Spec.position next = Spec.position start + width.val := by
  have hr := primitive_success ctx.status _ next value h
  unfold Ordering.outcome at hr
  split at hr
  · split at hr
    · obtain ⟨last, result, heq, hv, hp, _⟩ := hr
      cases heq
      exact ⟨hv, hp⟩
    · cases hr
  · cases hr

private theorem take_success (input : Slice U8) (ctx : ParseContext) (count : Usize)
    (start next : Cursor) (payload : Slice U8)
    (h : takeOutcome input ctx count start (.Success next payload)) :
    start.bit.val = 0 ∧ next.byte.val = start.byte.val + count.val ∧ next.bit = 0#u8 ∧
      payload.val = (input.val.drop start.byte.val).take count.val := by
  have hr := primitive_success ctx.status _ next payload h
  unfold Spec.takeAlignedOutcome at hr
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

theorem header_success (input : Slice U8) (ctx : ParseContext) (start next : Cursor)
    (header : Header) (h : headerOutcome input ctx start (.Success next header)) :
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

private theorem scope_success {α : Type} (length : Usize) (changed : Bool) (start next : Cursor)
    (child : ParseOutcome α → Prop) (value : α)
    (h : Ordering.scope length changed start child (.Success next value)) :
    child (.Success next value) := by
  cases changed
  · exact h
  · unfold Ordering.scope at h
    cases hg : Ordering.guard length start <;> simp only [hg] at h
    · obtain ⟨outcome, houtcome, heq⟩ := h
      cases outcome with
      | NeedMore => cases heq
      | Error error => cases heq
      | Success last result =>
        unfold Ordering.finish at heq
        cases he : Ordering.guard length last <;> simp only [he] at heq
        · cases heq; exact houtcome
        · cases heq
    · cases h

/-- Successful frames consume exactly 12 + payload length bytes. The borrowed
payload and CRC interval are exact slices of the original input. -/
theorem frame_success (input : Slice U8) (ctx : ParseContext) (lookup : U32 → Option U8)
    (start next : Cursor) (packet : Packet)
    (h : frameOutcome input ctx lookup start (.Success next packet)) :
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
  have hchild := scope_success _ _ _ _ _ _ h
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
  obtain ⟨_, hspan, hbody⟩ := Span.capture_success input bodyStart _ () () _ bodyEnd
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

private theorem primitive_final {α : Type} (contract : Spec.ParseResult α → Prop) :
    ¬Partial.primitive .Final contract .NeedMore := by
  rintro ⟨parsed, _, heq⟩
  cases parsed with
  | Ok pair => cases pair; cases heq
  | Err error => cases heq

private theorem map_not_more {α β : Type} (child : Cursor → ParseOutcome α → Prop)
    (mapping : α → β → Prop) (start : Cursor) (hc : ¬child start .NeedMore) :
    ¬Partial.map child mapping start .NeedMore := by
  rintro ⟨outcome, houtcome, hrest⟩
  cases outcome with
  | NeedMore => exact hc houtcome
  | Error error => cases hrest
  | Success next value => obtain ⟨_, _, heq⟩ := hrest; cases heq

private theorem verify_not_more {α : Type} (child : Cursor → ParseOutcome α → Prop)
    (predicate : α → Prop) [DecidablePred predicate] (start : Cursor)
    (hc : ¬child start .NeedMore) : ¬Partial.verify child predicate start .NeedMore := by
  rintro ⟨outcome, houtcome, hrest⟩
  cases outcome with
  | NeedMore => exact hc houtcome
  | Error error => cases hrest
  | Success next value =>
    change (if predicate value then ParseOutcome.NeedMore = .Success next value
      else ParseOutcome.NeedMore = ParseOutcome.Error (T := α) .Mismatch) at hrest
    split at hrest <;> cases hrest

private theorem sequence_not_more {α β : Type} (first : Cursor → ParseOutcome α → Prop)
    (second : Cursor → ParseOutcome β → Prop) (start : Cursor)
    (hf : ¬first start .NeedMore) (hs : ∀ next, ¬second next .NeedMore) :
    ¬Partial.sequence first second start .NeedMore := by
  rintro ⟨outcome, houtcome, hrest⟩
  cases outcome with
  | NeedMore => exact hf houtcome
  | Error error => cases hrest
  | Success next value =>
    obtain ⟨result, hresult, heq⟩ := hrest
    cases result with
    | NeedMore => exact hs next hresult
    | Error error => cases heq
    | Success last output => cases heq

private theorem bind_not_more {α β : Type} (first : Cursor → ParseOutcome α → Prop)
    (second : α → Cursor → ParseOutcome β → Prop) (start : Cursor)
    (hf : ¬first start .NeedMore) (hs : ∀ value next, ¬second value next .NeedMore) :
    ¬Partial.bind first second start .NeedMore := by
  rintro ⟨outcome, houtcome, hrest⟩
  cases outcome with
  | NeedMore => exact hf houtcome
  | Error error => cases hrest
  | Success next value => exact hs value next hrest

private theorem scope_not_more {α : Type} (length : Usize) (changed : Bool) (start : Cursor)
    (child : ParseOutcome α → Prop) (hc : ¬child .NeedMore) :
    ¬Ordering.scope length changed start child .NeedMore := by
  intro h
  cases changed
  · exact hc h
  · unfold Ordering.scope at h
    cases hg : Ordering.guard length start <;> simp only [hg] at h
    · obtain ⟨outcome, houtcome, heq⟩ := h
      cases outcome with
      | NeedMore => exact hc houtcome
      | Error error => cases heq
      | Success next value =>
        unfold Ordering.finish at heq
        cases he : Ordering.guard length next <;> simp [he] at heq
    · cases h

/-- Final input always yields a packet or an error; it cannot request more data. -/
theorem frame_final_not_more (input : Slice U8) (ctx : ParseContext)
    (lookup : U32 → Option U8) (start : Cursor) (hs : ctx.status = .Final) :
    ¬frameOutcome input ctx lookup start .NeedMore := by
  have hb (cursor : Cursor) :
      ¬byteOutcome input { ctx with order := wireOrder } cursor .NeedMore := by
    unfold byteOutcome
    rw [hs]
    exact primitive_final _
  have hi (width : U8) (cursor : Cursor) :
      ¬bitsOutcome input { ctx with order := wireOrder } width cursor .NeedMore := by
    unfold bitsOutcome
    rw [hs]
    exact primitive_final _
  have ht (count : Usize) (cursor : Cursor) :
      ¬takeOutcome input { ctx with order := wireOrder } count cursor .NeedMore := by
    unfold takeOutcome
    rw [hs]
    exact primitive_final _
  have hh (cursor : Cursor) :
      ¬headerOutcome input { ctx with order := wireOrder } cursor .NeedMore := by
    unfold headerOutcome headerFields
    apply map_not_more
    apply sequence_not_more
    · apply sequence_not_more
      · exact hb _
      · intro _
        apply sequence_not_more
        · exact verify_not_more _ _ _ (hb _)
        · intro _; exact hb _
    · intro _
      apply sequence_not_more
      · apply sequence_not_more
        · exact hb _
        · intro _
          apply sequence_not_more
          · exact verify_not_more _ _ _ (hb _)
          · intro _; exact verify_not_more _ _ _ (hb _)
      · intro _; exact hi _ _
  unfold frameOutcome
  apply scope_not_more
  apply map_not_more
  apply sequence_not_more
  · apply sequence_not_more
    · exact ht _ _
    · intro _; exact verify_not_more _ _ _ (hb _)
  · intro _
    apply map_not_more
    apply verify_not_more
    apply sequence_not_more
    · intro h
      have hc := Span.capture_need_more input _ wireOrder.bit () () _ h
      apply bind_not_more _ _ _ (hh _) _ hc
      intro header next
      exact map_not_more _ _ _ (ht _ _)
    · intro _
      exact map_not_more _ _ _ (hi _ _)

theorem mavlink_final_not_more {F : Type} (fi : core.ops.function.Fn F U32 (Option U8))
    (parser : MavlinkV2 F) (lookup : U32 → Option U8)
    (hf : lookupContract fi parser.crc_extra lookup) (input : Slice U8) (start : Cursor)
    (ctx : ParseContext) (hs : ctx.status = .Final) :
    (mavlinkInst fi).parse_with parser input start ctx ⦃ result => result ≠ .NeedMore ⦄ := by
  step with mavlink_spec fi parser lookup hf input start ctx as ⟨result, hr⟩
  intro heq
  subst result
  exact frame_final_not_more input ctx lookup start hs hr

/-- Exhausting an aligned payload requests more data precisely on partial input;
the same truncation is UnexpectedEnd once the buffer is declared final. -/
theorem payload_truncated (header : Header) (input : Slice U8) (start : Cursor)
    (ctx : ParseContext) (ha : start.bit.val = 0) (hv : start.byte.val ≤ input.val.length)
    (hshort : input.val.length < start.byte.val + header.payload_length.val) :
    payloadInst.parse_with ⟨header⟩ input start ctx ⦃ result => result =
      match ctx.status with | .Partial => .NeedMore | .Final => .Error .UnexpectedEnd ⦄ := by
  step with payload_spec ⟨header⟩ input start ctx as ⟨result, hr⟩
  obtain ⟨outcome, ⟨raw, hraw, houtcome⟩, hrest⟩ := hr
  have hcount : (UScalar.cast .Usize header.payload_length).val = header.payload_length.val := by
    scalar_tac
  have hbounds : start.bit.val < 8 ∧ start.byte.val ≤ input.val.length ∧
      (start.byte.val = input.val.length → start.bit.val = 0) := by omega
  simp only [Spec.takeAlignedOutcome, if_pos hbounds, if_pos ha, hcount,
    if_neg (Nat.not_le_of_lt hshort)] at hraw
  subst raw
  cases hs : ctx.status <;>
    simp_all only [Partial.primitiveResult, Spec.completedResult]

end
end RustHammer.Mavlink
