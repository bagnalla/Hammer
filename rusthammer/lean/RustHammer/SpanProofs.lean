import RustHammer.SpanSpec
import RustHammer.PartialProofs

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
theorem new_spec (input : Slice U8) (start finish : Cursor) (order : BitOrder) :
    BitSpan.new input start finish order
      ⦃ result => result = checked input start finish order ⦄ := by
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

theorem checked_success (input : Slice U8) (start finish : Cursor) (order : BitOrder)
    (span : BitSpan) (h : checked input start finish order = .Ok span) :
    valid span ∧ span = ⟨input, start, finish, order⟩ := by
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

theorem bit_order_spec (span : BitSpan) :
    BitSpan.impl.bit_order span ⦃ order => order = span.bit_order ⦄ := by
  simp [BitSpan.impl.bit_order, spec_ok]

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
subsequence of original bytes, independent of bit and byte decoding order. -/
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

/-- Generic backend proof: all child outcomes, state transitions, and the exact
input/context are preserved. Invalid entries require no child termination premise. -/
theorem with_span_eval_spec {State P α : Type} (inst : Eval P State α)
    (parser : WithSpan P) (state : State) (input : Slice U8) (cursor : Cursor) (ctx : ParseContext)
    (child : ParseOutcome α × State → Prop)
    (hp : validCursor input.val.length cursor →
      inst.eval parser.parser state input cursor ctx ⦃ result => child result ⦄) :
    WithSpan.Insts.RusthammerEvalInputBackendPairClause0_Clause0_OutputBitSpan.eval
      inst parser state input cursor ctx
      ⦃ result => capture input cursor ctx.order.bit state child result ⦄ := by
  unfold WithSpan.Insts.RusthammerEvalInputBackendPairClause0_Clause0_OutputBitSpan.eval
  step with cursor_valid_spec input.len cursor as ⟨allowed, hallowed⟩
  by_cases hv : validCursor input.val.length cursor
  · have ha : allowed = true := by simpa [hv] using hallowed
    simp only [ha, ↓reduceIte]
    step with hp hv as ⟨outcome, final, houtcome⟩
    cases outcome with
    | Success next value =>
      step with new_spec input cursor next ctx.order.bit as ⟨span, hspan⟩
      cases hcheck : checked input cursor next ctx.order.bit <;> simp only [hspan, hcheck, spec_ok]
      all_goals
        simp only [capture, if_pos hv]
        exact ⟨.Success next value, final, houtcome, by simp [attach, hcheck]⟩
    | Error error =>
      simp only [spec_ok, capture, if_pos hv]
      exact ⟨.Error error, final, houtcome, rfl⟩
    | NeedMore =>
      simp only [spec_ok, capture, if_pos hv]
      exact ⟨.NeedMore, final, houtcome, rfl⟩
  · have ha : allowed = false := by simpa [hv] using hallowed
    simp [ha, capture, hv, spec_ok]

theorem recognize_eval_spec {State P α : Type} (inst : Eval P State α)
    (parser : Recognize P) (state : State) (input : Slice U8) (cursor : Cursor) (ctx : ParseContext)
    (child : ParseOutcome α × State → Prop)
    (hp : validCursor input.val.length cursor →
      inst.eval parser.parser state input cursor ctx ⦃ result => child result ⦄) :
    Recognize.Insts.RusthammerEvalInputBackendBitSpan.eval inst parser state input cursor ctx
      ⦃ result => recognize input cursor ctx.order.bit state child result ⦄ := by
  unfold Recognize.Insts.RusthammerEvalInputBackendBitSpan.eval
  step with with_span_eval_spec (Shared0P.Insts.RusthammerEval inst) ⟨parser.parser⟩
    state input cursor ctx child hp as ⟨captured, final, hcaptured⟩
  cases captured <;> simp only [spec_ok]
  all_goals exact ⟨_, final, hcaptured, rfl⟩

theorem with_span_with_spec {P α : Type} (inst : DirectParser P α)
    (parser : WithSpan P) (input : Slice U8) (cursor : Cursor) (ctx : ParseContext)
    (child : ParseOutcome α → Prop)
    (hp : validCursor input.val.length cursor →
      inst.parse_with parser.parser input cursor ctx ⦃ result => child result ⦄) :
    DirectParser.parse_with (WithSpan.Insts.RusthammerEvalInputBackendPairClause0_Clause0_OutputBitSpan inst)
      parser input cursor ctx
      ⦃ result => capture input cursor ctx.order.bit () (fun pair => child pair.1) (result, ()) ⦄ := by
  apply direct_projection_spec
  apply with_span_eval_spec
  intro hv
  rw [eval_direct]
  step with hp hv as ⟨outcome, houtcome⟩
  simpa using houtcome

theorem recognize_with_spec {P α : Type} (inst : DirectParser P α)
    (parser : Recognize P) (input : Slice U8) (cursor : Cursor) (ctx : ParseContext)
    (child : ParseOutcome α → Prop)
    (hp : validCursor input.val.length cursor →
      inst.parse_with parser.parser input cursor ctx ⦃ result => child result ⦄) :
    DirectParser.parse_with (Recognize.Insts.RusthammerEvalInputBackendBitSpan inst) parser input cursor ctx
      ⦃ result => recognize input cursor ctx.order.bit () (fun pair => child pair.1) (result, ()) ⦄ := by
  apply direct_projection_spec
  apply recognize_eval_spec
  intro hv
  rw [eval_direct]
  step with hp hv as ⟨outcome, houtcome⟩
  simpa using houtcome

theorem capture_need_more {State α : Type} (input : Slice U8) (start : Cursor) (order : BitOrder)
    (state final : State) (child : ParseOutcome α × State → Prop)
    (h : capture input start order state child (.NeedMore, final)) : child (.NeedMore, final) := by
  unfold capture at h
  split at h
  · obtain ⟨outcome, nextState, hc, heq⟩ := h
    cases outcome with
    | Success next value =>
      unfold attach at heq
      cases hs : checked input start next order <;> simp [hs] at heq
    | Error error => simp [attach] at heq
    | NeedMore =>
      have he : final = nextState := by simpa [attach] using heq
      simpa [he] using hc
  · simp at h

theorem recognize_need_more {State α : Type} (input : Slice U8) (start : Cursor) (order : BitOrder)
    (state final : State) (child : ParseOutcome α × State → Prop)
    (h : recognize input start order state child (.NeedMore, final)) : child (.NeedMore, final) := by
  obtain ⟨captured, nextState, hc, heq⟩ := h
  cases captured with
  | Success next value => simp [discard] at heq
  | Error error => simp [discard] at heq
  | NeedMore =>
    have he : final = nextState := by simpa [discard] using heq
    subst nextState
    exact capture_need_more _ _ _ _ _ _ hc

/-- The complete-input API follows from the final child contract and the shared
default-method proof. No new NeedMore outcome is introduced by either wrapper. -/
theorem with_span_complete_spec {P α : Type} (inst : DirectParser P α)
    (parser : WithSpan P) (input : Slice U8) (cursor : Cursor)
    (child : ParseOutcome α → Prop)
    (hp : validCursor input.val.length cursor →
      inst.parse_with parser.parser input cursor ParseContext.FINAL ⦃ result => child result ⦄)
    (hfinal : ¬child .NeedMore) :
    DirectParser.parse (WithSpan.Insts.RusthammerEvalInputBackendPairClause0_Clause0_OutputBitSpan inst)
      parser input cursor
      ⦃ result => capture input cursor .HighFirst () (fun pair => child pair.1)
        (Spec.completedResult result, ()) ⦄ := by
  apply Proofs.complete_spec
  step with with_span_with_spec inst parser input cursor ParseContext.FINAL child hp as ⟨outcome, ho⟩
  simp only [ParseContext.FINAL, Order.DEFAULT] at ho
  cases outcome with
  | Success next value => exact ⟨.Ok (next, value), ho, rfl⟩
  | Error error => exact ⟨.Err error, ho, rfl⟩
  | NeedMore => exact False.elim (hfinal (capture_need_more _ _ _ _ _ _ ho))

theorem recognize_complete_spec {P α : Type} (inst : DirectParser P α)
    (parser : Recognize P) (input : Slice U8) (cursor : Cursor)
    (child : ParseOutcome α → Prop)
    (hp : validCursor input.val.length cursor →
      inst.parse_with parser.parser input cursor ParseContext.FINAL ⦃ result => child result ⦄)
    (hfinal : ¬child .NeedMore) :
    DirectParser.parse (Recognize.Insts.RusthammerEvalInputBackendBitSpan inst) parser input cursor
      ⦃ result => recognize input cursor .HighFirst () (fun pair => child pair.1)
        (Spec.completedResult result, ()) ⦄ := by
  apply Proofs.complete_spec
  step with recognize_with_spec inst parser input cursor ParseContext.FINAL child hp as ⟨outcome, ho⟩
  simp only [ParseContext.FINAL, Order.DEFAULT] at ho
  cases outcome with
  | Success next span => exact ⟨.Ok (next, span), ho, rfl⟩
  | Error error => exact ⟨.Err error, ho, rfl⟩
  | NeedMore => exact False.elim (hfinal (recognize_need_more _ _ _ _ _ _ ho))

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

/-- Every successful capture carries a valid span of exactly this input and
cursor interval, retaining the enclosing boundary direction. -/
theorem capture_success {State α : Type} (input : Slice U8) (start : Cursor) (order : BitOrder)
    (state final : State) (child : ParseOutcome α × State → Prop) (finish : Cursor)
    (value : α) (span : BitSpan)
    (h : capture input start order state child (.Success finish (value, span), final)) :
    valid span ∧ span = ⟨input, start, finish, order⟩ ∧ child (.Success finish value, final) := by
  unfold capture at h
  split at h
  · obtain ⟨outcome, nextState, hc, heq⟩ := h
    cases outcome with
    | Error error => simp [attach] at heq
    | NeedMore => simp [attach] at heq
    | Success next output =>
      unfold attach at heq
      cases hs : checked input start next order <;> simp only [hs] at heq
      · cases heq
        exact ⟨(checked_success _ _ _ _ _ hs).1, (checked_success _ _ _ _ _ hs).2, hc⟩
      · simp at heq
  · simp at h

/-- Mathematical offsets and physical source bits are inverse coordinates. -/
theorem offset_physical (order : BitOrder) (index : Nat) :
    offset order (physical order index).1 (physical order index).2 = index := by
  cases order <;> simp only [offset, physical] <;> omega

theorem physical_offset (order : BitOrder) (byte bit : Nat) (hb : bit < 8) :
    physical order (offset order byte bit) = (byte, bit) := by
  cases order <;> simp only [offset, physical, Prod.mk.injEq] <;> omega

theorem physical_injective (order : BitOrder) : Function.Injective (physical order) := by
  intro a b h
  have ho := congrArg (fun p => offset order p.1 p.2) h
  simpa only [offset_physical] using ho

/-- Counting distinct selected bits gives the mathematical cursor difference,
without assuming that either absolute position fits into a Rust usize. -/
theorem consumed_length (span : BitSpan) :
    (bits span).length = Spec.position span.end - Spec.position span.start := by
  simp [bits]

theorem bits_distinct (span : BitSpan) : (bits span).Nodup := by
  exact List.Nodup.map (physical_injective span.bit_order) (List.nodup_range')

theorem mem_bits (span : BitSpan) (byte bit : Nat) :
    (byte, bit) ∈ bits span ↔ selected span byte bit := by
  simp only [bits, List.mem_map]
  constructor
  · rintro ⟨index, hi, heq⟩
    have hb : bit < 8 := by
      cases ho : span.bit_order <;> simp [physical, ho, Prod.mk.injEq] at heq <;> omega
    have hoff : offset span.bit_order byte bit = index := by
      have h := congrArg (fun p => offset span.bit_order p.1 p.2) heq
      simpa only [offset_physical] using h.symm
    simp only [List.mem_range'_1] at hi
    exact ⟨hb, by rw [hoff]; omega, by rw [hoff]; omega⟩
  · rintro ⟨hb, hs, he⟩
    refine ⟨offset span.bit_order byte bit, ?_, physical_offset _ _ _ hb⟩
    simp only [List.mem_range'_1]
    omega

theorem selected_in_input (span : BitSpan) (hv : valid span) (byte bit : Nat)
    (h : selected span byte bit) : byte < span.input.val.length := by
  have he := hv.2.1.2
  rcases h with ⟨hb, hs, ht⟩
  cases ho : span.bit_order <;> simp only [offset, ho] at ht <;> omega

/-- A same-byte high-first span selects [8 - end.bit, 8 - start.bit). -/
theorem high_same_byte (span : BitSpan) (hv : valid span)
    (ho : span.bit_order = .HighFirst) (he : span.end.byte = span.start.byte) (bit : Nat) :
    selected span span.start.byte.val bit ↔
      8 - span.end.bit.val ≤ bit ∧ bit < 8 - span.start.bit.val := by
  have hs := hv.1.1
  have ht := hv.2.1.1
  simp only [selected, offset, ho, Spec.position, he]
  omega

theorem low_same_byte (span : BitSpan) (hv : valid span)
    (ho : span.bit_order = .LowFirst) (he : span.end.byte = span.start.byte) (bit : Nat) :
    selected span span.start.byte.val bit ↔
      span.start.bit.val ≤ bit ∧ bit < span.end.bit.val := by
  have ht := hv.2.1.1
  simp only [selected, offset, ho, Spec.position, he]
  omega

/-- For crossing spans, whole interior bytes are selected in either direction. -/
theorem interior_byte (span : BitSpan) (hv : valid span) (byte bit : Nat)
    (hs : span.start.byte.val < byte) (he : byte < span.end.byte.val) :
    selected span byte bit ↔ bit < 8 := by
  have hb := hv.1.1
  cases ho : span.bit_order <;> simp only [selected, offset, ho, Spec.position] <;> omega

/-- Crossing spans select only the unread portion of the first byte. -/
theorem crossing_start (span : BitSpan) (hv : valid span) (bit : Nat)
    (hc : span.start.byte.val < span.end.byte.val) :
    selected span span.start.byte.val bit ↔ bit < 8 ∧
      (match span.bit_order with
        | .HighFirst => bit < 8 - span.start.bit.val
        | .LowFirst => span.start.bit.val ≤ bit) := by
  have hs := hv.1.1
  cases ho : span.bit_order <;> simp only [selected, offset, ho, Spec.position] <;> omega

/-- The final boundary selects only the consumed portion, including no bits
at an aligned end. This also covers canonical end-of-input. -/
theorem crossing_end (span : BitSpan) (hv : valid span) (bit : Nat)
    (hc : span.start.byte.val < span.end.byte.val) :
    selected span span.end.byte.val bit ↔ bit < 8 ∧
      (match span.bit_order with
        | .HighFirst => 8 - span.end.bit.val ≤ bit
        | .LowFirst => bit < span.end.bit.val) := by
  have hs := hv.1.1
  have he := hv.2.1.1
  cases ho : span.bit_order <;> simp only [selected, offset, ho, Spec.position] <;> omega

/-- Aligned spans select precisely all the physical bits of their raw byte view. -/
theorem aligned_region (span : BitSpan) (byte bit : Nat)
    (hs : span.start.bit.val = 0) (he : span.end.bit.val = 0) :
    selected span byte bit ↔
      span.start.byte.val ≤ byte ∧ byte < span.end.byte.val ∧ bit < 8 := by
  cases ho : span.bit_order <;>
    simp only [selected, offset, ho, Spec.position, hs, he] <;> omega

end
end RustHammer.Span
