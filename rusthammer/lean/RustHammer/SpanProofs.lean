import RustHammer.SpanSpec
import RustHammer.ParserProofs

open RustHammer.Code.grammar.span
  RustHammer.Code.input_types
  RustHammer.Code.parser_traits
  RustHammer.Code.span_types

open Aeneas Aeneas.Std Result WP

namespace RustHammer.Span
noncomputable section
open Classical Code

theorem cursor_valid_spec (length : Usize) (cursor : Cursor) :
    span_cursor_valid length cursor
      ⦃ result => result = decide (validCursor length.val cursor) ⦄ := by
  unfold span_cursor_valid
  by_cases hb : cursor.bit < 8#u8 <;> by_cases hl : cursor.byte < length <;>
    by_cases he : cursor.byte = length <;> by_cases hz : cursor.bit = 0#u8 <;>
    simp [hb, hl, he, hz, spec_ok, validCursor, Spec.validPosition, Spec.position] <;> scalar_tac

/-- Total constructor contract, including invalid raw cursors and empty spans. -/
theorem new_spec (input : Slice U8) (start finish : Cursor) :
    BitSpan.new input start finish
      ⦃ result => result = checked input start finish ⦄ := by
  unfold BitSpan.new
  step with cursor_valid_spec input.len start as ⟨first, hfirst⟩
  by_cases hs : validCursor input.val.length start
  · have hf : first = true := by simpa [hs] using hfirst
    simp only [hf, ↓reduceIte]
    step with cursor_valid_spec input.len finish as ⟨last, hlast⟩
    by_cases he : validCursor input.val.length finish
    · have hl : last = true := by simpa [he] using hlast
      simp only [hl, ↓reduceIte]
      have hsb := hs.1
      have heb := he.1
      have hbounds : validCursor input.val.length start ∧ validCursor input.val.length finish := ⟨hs, he⟩
      simp only [checked, if_pos hbounds]
      by_cases hb : finish.byte < start.byte <;>
        by_cases hbyte : finish.byte = start.byte <;>
        by_cases hbit : finish.bit < start.bit
      all_goals
        simp [hb, hbyte, hbit, spec_ok]
        unfold Spec.position
        scalar_tac
    · have hl : last = false := by simpa [he] using hlast
      simp [hl, checked, he, spec_ok]
  · have hf : first = false := by simpa [hs] using hfirst
    simp [hf, checked, hs, spec_ok]

theorem checked_success (input : Slice U8) (start finish : Cursor)
    (span : BitSpan) (h : checked input start finish = .Ok span) :
    valid span ∧ span = ⟨input, start, finish⟩ := by
  unfold checked at h
  split at h
  · rename_i hb
    split at h
    · rename_i ho
      cases h
      exact ⟨⟨hb.1, hb.2, ho⟩, rfl⟩
    · contradiction
  · contradiction

theorem input_spec (span : BitSpan) :
    BitSpan.impl.input span ⦃ input => input = span.input ⦄ := by
  simp [BitSpan.impl.input, spec_ok]

theorem start_spec (span : BitSpan) :
    BitSpan.impl.start span ⦃ start => start = span.start ⦄ := by
  simp [BitSpan.impl.start, spec_ok]

theorem end_spec (span : BitSpan) :
    BitSpan.impl.end span ⦃ finish => finish = span.end ⦄ := by
  simp [BitSpan.impl.end, spec_ok]

theorem clone_spec (span : BitSpan) :
    BitSpan.Insts.CoreCloneClone.clone span ⦃ copied => copied = span ⦄ := by
  simp [BitSpan.Insts.CoreCloneClone.clone, spec_ok]

theorem is_empty_spec (span : BitSpan) (hv : valid span) :
    BitSpan.is_empty span
      ⦃ result => result = decide (Spec.position span.start = Spec.position span.end) ⦄ := by
  have hs := hv.1.1
  have he := hv.2.1.1
  by_cases hb : span.start.byte = span.end.byte <;>
    by_cases hbit : span.start.bit = span.end.bit <;>
    simp [BitSpan.is_empty, hb, hbit, spec_ok, Spec.position] <;> scalar_tac

/-- Indexing is proved safe from the span invariant; the result is the exact
subsequence of original bytes, independent of byte decoding order. -/
theorem as_bytes_spec (span : BitSpan) (hv : valid span) :
    BitSpan.as_bytes span ⦃ result => byteView span result ⦄ := by
  by_cases hs : span.start.bit = 0#u8 <;> by_cases he : span.end.bit = 0#u8
  · have hsb : span.start.bit.val = 0 := by scalar_tac
    have heb : span.end.bit.val = 0 := by scalar_tac
    have hbounds := hv
    unfold valid validCursor Spec.validPosition Spec.position at hbounds
    simp only [BitSpan.as_bytes, hs, he, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    step as ⟨bytes, hbytes, hlen⟩
    simp only [byteView, hsb, heb, and_self, ↓reduceIte]
    exact ⟨bytes, rfl, by simpa [List.slice] using hbytes⟩
  all_goals
    simp [BitSpan.as_bytes, hs, he, byteView, spec_ok]
    scalar_tac

/-- Invalid entries require no child termination premise. Child failures are
preserved, and successful endpoints are validated before attaching the span. -/
theorem with_span_with_spec {P α : Type} (inst : parser_traits.Parser P α)
    (parser : WithSpan P) (input : Slice U8) (cursor : Cursor) (order : ByteOrder)
    (child : Spec.ParseResult α → Prop)
    (hp : validCursor input.val.length cursor →
      inst.parse_with parser.parser input cursor order ⦃ result => child result ⦄) :
    WithSpan.Insts.RusthammerParser_traitsParserInputPairClause0_OutputBitSpan.parse_with
      inst parser input cursor order
      ⦃ result => capture input cursor child result ⦄ := by
  unfold WithSpan.Insts.RusthammerParser_traitsParserInputPairClause0_OutputBitSpan.parse_with
  step with cursor_valid_spec input.len cursor as ⟨allowed, hallowed⟩
  by_cases hv : validCursor input.val.length cursor
  · have ha : allowed = true := by simpa [hv] using hallowed
    simp only [ha, ↓reduceIte]
    step with hp hv as ⟨outcome, houtcome⟩
    cases outcome with
    | Ok pair =>
      rcases pair with ⟨next, value⟩
      step with new_spec input cursor next as ⟨span, hspan⟩
      cases hcheck : checked input cursor next <;> simp only [hspan, hcheck, spec_ok]
      all_goals
        simp only [capture, if_pos hv]
        exact ⟨.Ok (next, value), houtcome, by simp [attach, hcheck]⟩
    | Err error =>
      simp only [spec_ok, capture, if_pos hv]
      exact ⟨.Err error, houtcome, rfl⟩
  · have ha : allowed = false := by simpa [hv] using hallowed
    simp [ha, capture, hv, spec_ok]

theorem recognize_with_spec {P α : Type} (inst : parser_traits.Parser P α)
    (parser : Recognize P) (input : Slice U8) (cursor : Cursor) (order : ByteOrder)
    (child : Spec.ParseResult α → Prop)
    (hp : validCursor input.val.length cursor →
      inst.parse_with parser.parser input cursor order ⦃ result => child result ⦄) :
    Recognize.Insts.RusthammerParser_traitsParserInputBitSpan.parse_with inst parser input cursor order
      ⦃ result => recognize input cursor child result ⦄ := by
  unfold Recognize.Insts.RusthammerParser_traitsParserInputBitSpan.parse_with
  step with with_span_with_spec (Shared0P.Insts.RusthammerParser_traitsParser inst) ⟨parser.parser⟩
    input cursor order child hp as ⟨captured, hcaptured⟩
  cases captured with
  | Ok pair =>
    rcases pair with ⟨next, value, span⟩
    exact ⟨_, hcaptured, rfl⟩
  | Err error =>
    simp only [spec_ok]
    exact ⟨_, hcaptured, rfl⟩

/-- The convenience entry point supplies the default byte order. -/
theorem with_span_complete_spec {P α : Type} (inst : parser_traits.Parser P α)
    (parser : WithSpan P) (input : Slice U8) (cursor : Cursor)
    (child : Spec.ParseResult α → Prop)
    (hp : validCursor input.val.length cursor →
      inst.parse_with parser.parser input cursor ByteOrder.Big ⦃ result => child result ⦄) :
    parser_traits.Parser.parse.default
      (WithSpan.Insts.RusthammerParser_traitsParserInputPairClause0_OutputBitSpan inst)
      parser input cursor ⦃ result => capture input cursor child result ⦄ := by
  exact with_span_with_spec inst parser input cursor .Big child hp

theorem recognize_complete_spec {P α : Type} (inst : parser_traits.Parser P α)
    (parser : Recognize P) (input : Slice U8) (cursor : Cursor)
    (child : Spec.ParseResult α → Prop)
    (hp : validCursor input.val.length cursor →
      inst.parse_with parser.parser input cursor ByteOrder.Big ⦃ result => child result ⦄) :
    parser_traits.Parser.parse.default
      (Recognize.Insts.RusthammerParser_traitsParserInputBitSpan inst) parser input cursor
      ⦃ result => recognize input cursor child result ⦄ := by
  exact recognize_with_spec inst parser input cursor .Big child hp

theorem with_span_clone_spec {P : Type} (inst : core.clone.Clone P) (parser : WithSpan P)
    (copy : P → Prop) (hp : inst.clone parser.parser ⦃ copied => copy copied ⦄) :
    WithSpan.Insts.CoreCloneClone.clone inst parser ⦃ copied => copy copied.parser ⦄ := by
  unfold WithSpan.Insts.CoreCloneClone.clone
  step with hp as ⟨copied, hc⟩
  simpa using hc

theorem recognize_clone_spec {P : Type} (inst : core.clone.Clone P) (parser : Recognize P)
    (copy : P → Prop) (hp : inst.clone parser.parser ⦃ copied => copy copied ⦄) :
    Recognize.Insts.CoreCloneClone.clone inst parser ⦃ copied => copy copied.parser ⦄ := by
  unfold Recognize.Insts.CoreCloneClone.clone
  step with hp as ⟨copied, hc⟩
  simpa using hc

/-- Every successful capture carries a valid span of exactly this input and cursor interval. -/
theorem capture_success {α : Type} (input : Slice U8) (start : Cursor)
    (child : Spec.ParseResult α → Prop) (finish : Cursor) (value : α) (span : BitSpan)
    (h : capture input start child (.Ok (finish, (value, span)))) :
    valid span ∧ span = ⟨input, start, finish⟩ ∧ child (.Ok (finish, value)) := by
  unfold capture at h
  split at h
  · obtain ⟨outcome, hc, heq⟩ := h
    cases outcome with
    | Err error => simp [attach] at heq
    | Ok pair =>
      rcases pair with ⟨next, output⟩
      unfold attach at heq
      cases hs : checked input start next <;> simp only [hs] at heq
      · cases heq
        exact ⟨(checked_success _ _ _ _ hs).1, (checked_success _ _ _ _ hs).2, hc⟩
      · simp at heq
  · simp at h

/-- Mathematical offsets and physical source bits are inverse coordinates. -/
theorem offset_physical (index : Nat) :
    offset (physical index).1 (physical index).2 = index := by
  simp only [offset, physical] ; omega

theorem physical_offset (byte bit : Nat) (hb : bit < 8) :
    physical (offset byte bit) = (byte, bit) := by
  simp only [offset, physical, Prod.mk.injEq] ; omega

theorem physical_injective : Function.Injective (physical) := by
  intro a b h
  have ho := congrArg (fun p => offset p.1 p.2) h
  simpa only [offset_physical] using ho

/-- Counting distinct selected bits gives the mathematical cursor difference,
without assuming that either absolute position fits into a Rust usize. -/
theorem consumed_length (span : BitSpan) :
    (bits span).length = Spec.position span.end - Spec.position span.start := by
  simp [bits]

theorem bits_distinct (span : BitSpan) : (bits span).Nodup := by
  exact List.Nodup.map (physical_injective) (List.nodup_range')

theorem mem_bits (span : BitSpan) (byte bit : Nat) :
    (byte, bit) ∈ bits span ↔ selected span byte bit := by
  simp only [bits, List.mem_map]
  constructor
  · rintro ⟨index, hi, heq⟩
    have hb : bit < 8 := by
      simp [physical, Prod.mk.injEq] at heq ; omega
    have hoff : offset byte bit = index := by
      have h := congrArg (fun p => offset p.1 p.2) heq
      simpa only [offset_physical] using h.symm
    simp only [List.mem_range'_1] at hi
    exact ⟨hb, by rw [hoff]; omega, by rw [hoff]; omega⟩
  · rintro ⟨hb, hs, he⟩
    refine ⟨offset byte bit, ?_, physical_offset _ _ hb⟩
    simp only [List.mem_range'_1]
    omega

theorem selected_in_input (span : BitSpan) (hv : valid span) (byte bit : Nat)
    (h : selected span byte bit) : byte < span.input.val.length := by
  have he := hv.2.1.2
  rcases h with ⟨hb, hs, ht⟩
  simp only [offset] at ht ; omega

/-- A same-byte high-first span selects [8 - end.bit, 8 - start.bit). -/
theorem high_same_byte (span : BitSpan) (hv : valid span)
    (he : span.end.byte = span.start.byte) (bit : Nat) :
    selected span span.start.byte.val bit ↔
      8 - span.end.bit.val ≤ bit ∧ bit < 8 - span.start.bit.val := by
  have hs := hv.1.1
  have ht := hv.2.1.1
  simp only [selected, offset, Spec.position, he]
  omega

/-- For crossing spans, whole interior bytes are selected . -/
theorem interior_byte (span : BitSpan) (hv : valid span) (byte bit : Nat)
    (hs : span.start.byte.val < byte) (he : byte < span.end.byte.val) :
    selected span byte bit ↔ bit < 8 := by
  have hb := hv.1.1
  simp only [selected, offset, Spec.position] ; omega

/-- Crossing spans select only the unread portion of the first byte. -/
theorem crossing_start (span : BitSpan) (hv : valid span) (bit : Nat)
    (hc : span.start.byte.val < span.end.byte.val) :
    selected span span.start.byte.val bit ↔ bit < 8 ∧
      bit < 8 - span.start.bit.val := by
  have hs := hv.1.1
  simp only [selected, offset, Spec.position] ; omega

/-- The final boundary selects only the consumed portion, including no bits
at an aligned end. This also covers canonical end-of-input. -/
theorem crossing_end (span : BitSpan) (hv : valid span) (bit : Nat)
    (hc : span.start.byte.val < span.end.byte.val) :
    selected span span.end.byte.val bit ↔ bit < 8 ∧
      8 - span.end.bit.val ≤ bit := by
  have hs := hv.1.1
  have he := hv.2.1.1
  simp only [selected, offset, Spec.position] ; omega

/-- Aligned spans select precisely all the physical bits of their raw byte view. -/
theorem aligned_region (span : BitSpan) (byte bit : Nat)
    (hs : span.start.bit.val = 0) (he : span.end.bit.val = 0) :
    selected span byte bit ↔
      span.start.byte.val ≤ byte ∧ byte < span.end.byte.val ∧ bit < 8 := by
  simp only [selected, offset, Spec.position, hs, he] ; omega

end
end RustHammer.Span
