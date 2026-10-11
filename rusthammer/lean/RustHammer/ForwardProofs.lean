import RustHammer.MavlinkProperties
import RustHammer.SepByProperties
import RustHammer.CompositionProofs
import RustHammer.MatchProofs

open Aeneas Aeneas.Std Result WP
open RustHammer.Code.input_types

namespace RustHammer.Forward

/-- The v1 cursor law applies to successful parses starting at valid positions.
It is an explicit contract for custom parsers, not an assumption about every Rust trait instance. -/
def Preserves {α : Type} (input : Slice U8)
    (child : Cursor → Spec.ParseResult α → Prop) : Prop :=
  ∀ start next value, Spec.validCursor input start → child start (.Ok (next, value)) →
    Spec.validCursor input next ∧ Spec.position start ≤ Spec.position next

theorem primitive {α : Type} (input : Slice U8)
    (child : Cursor → Spec.ParseResult α → Prop) (hp : Preserves input child) :
    Preserves input (fun start => Contracts.primitive (child start)) := by
  rintro start next value hv ⟨result, hc, heq⟩
  subst result
  exact hp _ _ _ hv hc

theorem bit (input : Slice U8) : Preserves input (Spec.bitOutcome input) := by
  intro start next value _ h
  unfold Spec.bitOutcome at h
  split at h
  · rename_i readable
    obtain ⟨after, output, heq, hb, ht, _⟩ := h
    cases heq
    simp only [Spec.validCursor, Spec.position, hb, ht]
    split <;> omega
  · cases h

theorem bits (input : Slice U8) (width : U8) (order : ByteOrder) :
    Preserves input (fun start => Ordering.outcome input start width order) := by
  intro start next value hv h
  simp only [Ordering.outcome, if_pos hv] at h
  split at h
  · obtain ⟨after, output, heq, hn, hp, _⟩ := h
    cases heq
    exact ⟨hn, by omega⟩
  · cases h

theorem literal (input : Slice U8) (width : U8) (expected : U64) (order : ByteOrder) :
    Preserves input (fun start => Ordering.literalOutcome input start width expected order) := by
  rintro start next value hv ⟨numeric, hn, hr⟩
  cases numeric with
  | Err error => cases hr
  | Ok pair =>
    rcases pair with ⟨after, output⟩
    by_cases heq : output.val = expected.val
    · simp only [Spec.literalResult, heq, ↓reduceIte] at hr
      cases hr
      exact bits input width order _ _ _ hv hn
    · simp only [Spec.literalResult, heq, ↓reduceIte] at hr
      cases hr

theorem signed_bits (input : Slice U8) (width : U8) (order : ByteOrder) :
    Preserves input (fun start => Ordering.signedBitsOutcome input start width order) := by
  intro start next value hv h
  simp only [Ordering.signedBitsOutcome, if_pos hv] at h
  split at h
  · obtain ⟨after, output, heq, hn, hp, _⟩ := h
    cases heq
    exact ⟨hn, by omega⟩
  · cases h

theorem unsigned_integer (input : Slice U8) (ty : UScalarTy) (order : ByteOrder) :
    Preserves input (fun start => Ordering.unsignedIntegerOutcome ty input start order) := by
  intro start next value hv h
  simp only [Ordering.unsignedIntegerOutcome, if_pos hv] at h
  split at h
  · obtain ⟨after, output, heq, hn, hp, _⟩ := h
    cases heq
    exact ⟨hn, by omega⟩
  · cases h

theorem signed_integer (input : Slice U8) (ty : IScalarTy) (order : ByteOrder) :
    Preserves input (fun start => Ordering.signedIntegerOutcome ty input start order) := by
  intro start next value hv h
  simp only [Ordering.signedIntegerOutcome, if_pos hv] at h
  split at h
  · obtain ⟨after, output, heq, hn, hp, _⟩ := h
    cases heq
    exact ⟨hn, by omega⟩
  · cases h

theorem matched_bytes (input : Slice U8) (order : ByteOrder) (pattern : List U8) :
    Preserves input (Ordering.matchBytes input order pattern) := by
  induction pattern with
  | nil =>
    intro start next value hv h
    cases h
    exact ⟨hv, le_rfl⟩
  | cons expected rest ih =>
    rintro start next value hv ⟨decoded, hd, hr⟩
    cases decoded with
    | Err error => cases hr
    | Ok pair =>
      rcases pair with ⟨middle, byte⟩
      dsimp only at hr
      split at hr
      · have hm := primitive input _ (unsigned_integer input .U8 order) _ _ _ hv hd
        have hn := ih _ _ _ hm.1 hr
        exact ⟨hn.1, hm.2.trans hn.2⟩
      · cases hr

theorem byte_pattern (input : Slice U8) (order : ByteOrder) (pattern : Slice U8) :
    Preserves input (Ordering.bytePatternOutcome input order pattern) := by
  intro start next value hv h
  exact matched_bytes input order pattern.val _ _ _ hv h.2

theorem take_aligned (input : Slice U8) (count : Usize) :
    Preserves input (fun start => Spec.takeAlignedOutcome input start count) := by
  intro start next value _ h
  unfold Spec.takeAlignedOutcome at h
  split at h
  · split at h
    · rename_i aligned
      split at h
      · rename_i fits
        obtain ⟨after, output, heq, hb, ht, _⟩ := h
        cases heq
        simp only [Spec.validCursor, Spec.position, hb, ht, UScalar.ofNatCore_val_eq, aligned]
        omega
      · cases h
    · cases h
  · cases h

theorem skip_bits (input : Slice U8) (count : Usize) :
    Preserves input (fun start => Spec.skipBitsOutcome input start count) := by
  intro start next value _ h
  cases value
  have hp := Proofs.skip_bits_success input start next count ⟨_, h, rfl⟩
  exact ⟨hp.2.1, by omega⟩

theorem epsilon (input : Slice U8) : Preserves input Contracts.epsilon := by
  rintro start next value hv h
  cases h
  exact ⟨hv, le_rfl⟩

theorem fail (input : Slice U8) (α : Type) :
    Preserves input (fun _ => @Contracts.fail α) := by
  intro start next value hv h
  cases h

theorem tell (input : Slice U8) : Preserves input (Spec.tellOutcome input) := by
  intro start next value hv h
  simp only [Spec.tellOutcome, if_pos hv] at h
  cases h
  exact ⟨hv, le_rfl⟩

theorem end_of_input (input : Slice U8) : Preserves input (Spec.endOutcome input) := by
  intro start next value hv h
  simp only [Spec.endOutcome, if_pos hv] at h
  split at h
  · cases h; exact ⟨hv, le_rfl⟩
  · cases h

theorem sequence {α β : Type} (input : Slice U8)
    (first : Cursor → Spec.ParseResult α → Prop) (second : Cursor → Spec.ParseResult β → Prop)
    (hf : Preserves input first) (hs : Preserves input second) :
    Preserves input (Contracts.sequence first second) := by
  rintro start next ⟨a, b⟩ hv h
  obtain ⟨middle, hfirst, hsecond⟩ := Proofs.sequence_success_children _ _ _ _ _ _ h
  have hm := hf _ _ _ hv hfirst
  have hn := hs _ _ _ hm.1 hsecond
  exact ⟨hn.1, hm.2.trans hn.2⟩

/-- Every parser constructed by a successful Bind factory must satisfy the same cursor law. -/
theorem bind {α β : Type} (input : Slice U8)
    (first : Cursor → Spec.ParseResult α → Prop)
    (second : α → Cursor → Spec.ParseResult β → Prop)
    (hf : Preserves input first) (hs : ∀ value, Preserves input (second value)) :
    Preserves input (Contracts.bind first second) := by
  intro start next value hv h
  obtain ⟨middle, prior, hfirst, hsecond⟩ := Proofs.bind_success_children _ _ _ _ _ h
  have hm := hf _ _ _ hv hfirst
  have hn := hs prior _ _ _ hm.1 hsecond
  exact ⟨hn.1, hm.2.trans hn.2⟩

theorem map {α β : Type} (input : Slice U8) (child : Cursor → Spec.ParseResult α → Prop)
    (mapping : α → β → Prop) (hp : Preserves input child) :
    Preserves input (Contracts.map child mapping) := by
  intro start next value hv h
  obtain ⟨prior, hchild, _⟩ := Proofs.map_success_value _ _ _ _ _ h
  exact hp _ _ prior hv hchild

theorem try_map {α β ε : Type} (input : Slice U8)
    (child : Cursor → Spec.ParseResult α → Prop)
    (mapping : α → core.result.Result β ε → Prop) (hp : Preserves input child) :
    Preserves input (Contracts.tryMap child mapping) := by
  intro start next value hv h
  obtain ⟨prior, hchild, _⟩ := Proofs.try_map_success_child _ _ _ _ _ h
  exact hp _ _ prior hv hchild

theorem verify {α : Type} (input : Slice U8) (child : Cursor → Spec.ParseResult α → Prop)
    (predicate : α → Prop) [DecidablePred predicate] (hp : Preserves input child) :
    Preserves input (Contracts.verify child predicate) := by
  rintro start next value hv ⟨parsed, hc, hr⟩
  cases parsed with
  | Err error => cases hr
  | Ok pair =>
    rcases pair with ⟨after, output⟩
    dsimp only at hr
    split at hr
    · cases hr; exact hp _ _ _ hv hc
    · cases hr

theorem choice {α : Type} (input : Slice U8)
    (first second : Cursor → Spec.ParseResult α → Prop)
    (hf : Preserves input first) (hs : Preserves input second) :
    Preserves input (Contracts.choice first second) := by
  rintro start next value hv ⟨parsed, hc, hr⟩
  cases parsed with
  | Ok pair => cases hr; exact hf _ _ _ hv hc
  | Err error =>
    dsimp only at hr
    split at hr
    · exact hs _ _ _ hv hr
    · cases hr

theorem optional {α : Type} (input : Slice U8)
    (child : Cursor → Spec.ParseResult α → Prop) (hp : Preserves input child) :
    Preserves input (Contracts.optional child) := by
  rintro start next value hv ⟨parsed, hc, hr⟩
  cases parsed with
  | Ok pair => cases pair; cases hr; exact hp _ _ _ hv hc
  | Err error =>
    dsimp only at hr
    split at hr
    · cases hr; exact ⟨hv, le_rfl⟩
    · cases hr

theorem and (input : Slice U8) {α : Type} (child : Cursor → Spec.ParseResult α → Prop) :
    Preserves input (Contracts.and child) := by
  rintro start next value hv ⟨parsed, _, hr⟩
  cases parsed with
  | Ok pair => cases pair; cases hr; exact ⟨hv, le_rfl⟩
  | Err error => cases hr

theorem not (input : Slice U8) {α : Type} (child : Cursor → Spec.ParseResult α → Prop) :
    Preserves input (Contracts.not child) := by
  rintro start next value hv ⟨parsed, _, hr⟩
  cases parsed with
  | Ok pair => cases pair; cases hr
  | Err error =>
    dsimp only at hr
    split at hr
    · cases hr; exact ⟨hv, le_rfl⟩
    · cases hr

theorem left {α β : Type} (input : Slice U8)
    (first : Cursor → Spec.ParseResult α → Prop) (second : Cursor → Spec.ParseResult β → Prop)
    (hf : Preserves input first) (hs : Preserves input second) :
    Preserves input (Contracts.left first second) :=
  map input _ _ (sequence input first second hf hs)

theorem right {α β : Type} (input : Slice U8)
    (first : Cursor → Spec.ParseResult α → Prop) (second : Cursor → Spec.ParseResult β → Prop)
    (hf : Preserves input first) (hs : Preserves input second) :
    Preserves input (Contracts.right first second) :=
  map input _ _ (sequence input first second hf hs)

theorem middle {α β γ : Type} (input : Slice U8)
    (first : Cursor → Spec.ParseResult α → Prop) (child : Cursor → Spec.ParseResult β → Prop)
    (last : Cursor → Spec.ParseResult γ → Prop)
    (hf : Preserves input first) (hc : Preserves input child) (hl : Preserves input last) :
    Preserves input (Contracts.middle first child last) :=
  map input _ _ (sequence input first _ hf (sequence input child last hc hl))

theorem ignore {α : Type} (input : Slice U8) (child : Cursor → Spec.ParseResult α → Prop)
    (hp : Preserves input child) : Preserves input (Contracts.ignore child) := map input _ _ hp

theorem match_restriction {α β : Type} (input : Slice U8) (allowEqual : Bool)
    (first : Cursor → Spec.ParseResult α → Prop) (second : Cursor → Spec.ParseResult β → Prop)
    (hf : Preserves input first) :
    Preserves input (Contracts.matchRestriction allowEqual first second) := by
  intro start next value hv h
  exact hf _ _ _ hv (Proofs.match_restriction_success _ _ _ _ _ _ h).1

theorem exclusive {α : Type} (input : Slice U8)
    (first second : Cursor → Spec.ParseResult α → Prop)
    (hf : Preserves input first) (hs : Preserves input second) :
    Preserves input (Contracts.exclusive first second) := by
  intro start next value hv h
  rcases Proofs.xor_success _ _ _ _ _ h with h | h
  · exact hf _ _ _ hv h.1
  · exact hs _ _ _ hv h.1

/-- Span validation itself enforces the cursor law, even for a custom child. -/
theorem capture {α : Type} (input : Slice U8)
    (child : Cursor → Spec.ParseResult α → Prop) :
    Preserves input (fun start => Span.capture input start (child start)) := by
  rintro start next ⟨value, span⟩ _ h
  obtain ⟨hv, rfl, _⟩ := Span.capture_success _ _ _ _ _ _ h
  exact ⟨hv.2.1, hv.2.2⟩

theorem recognize {α : Type} (input : Slice U8)
    (child : Cursor → Spec.ParseResult α → Prop) :
    Preserves input (fun start => Span.recognize input start (child start)) := by
  rintro start next span hv ⟨captured, hc, hr⟩
  cases captured with
  | Err error => cases hr
  | Ok pair =>
    rcases pair with ⟨after, value, capturedSpan⟩
    cases hr
    exact capture input child _ _ _ hv hc

/-- The shared loop relation covers ordinary and separated repetition, with
collection or folding. Empty finite repetitions preserve their valid entry. -/
theorem indexed_repetitions {α : Type} (input : Slice U8)
    (child : Nat → Cursor → Spec.ParseResult α → Prop)
    (hp : ∀ count, Preserves input (child count)) (start next : Cursor) (values : List α)
    (hv : Spec.validCursor input start) (h : Spec.indexedRepetitions child start values next) :
    Spec.validCursor input next ∧ Spec.position start ≤ Spec.position next := by
  induction h with
  | empty => exact ⟨hv, le_rfl⟩
  | append prior last ih =>
    have hn := hp _ _ _ _ ih.1 last
    exact ⟨hn.1, ih.2.trans hn.2⟩

theorem bounded_iterations {α : Type} (input : Slice U8)
    (child : Nat → Cursor → Spec.ParseResult α → Prop) (min max : Nat)
    (hp : ∀ count, Preserves input (child count)) :
    Preserves input (Spec.boundedIterations child min max) := by
  intro start next values hv h
  exact indexed_repetitions input child hp start next values hv h.2.2.1

theorem unbounded_iterations {α : Type} (input : Slice U8)
    (child : Nat → Cursor → Spec.ParseResult α → Prop) (min : Nat) :
    Preserves input (Spec.unboundedIterations input child min) := by
  intro start next values hv h
  simp only [Spec.unboundedIterations, if_pos hv] at h
  apply indexed_repetitions input (fun n => Spec.advancing input (child n)) _ start next values hv h.2.1
  intro count before after value _ hc
  exact ⟨hc.2.1, hc.2.2.le⟩

theorem accumulated {α R : Type} (input : Slice U8) (invariant : List α → R → Prop)
    (repetition : Cursor → Spec.ParseResult (List α) → Prop) (hp : Preserves input repetition) :
    Preserves input (fun start => Spec.accumulated invariant (repetition start)) := by
  rintro start next state hv ⟨values, _, hr⟩
  exact hp _ _ values hv hr

/-- The extracted parser theorem supplies execution; the success theorem supplies
validity and exact forward consumption under the dialect callback contract. -/
theorem mavlink (input : Slice U8) (order : ByteOrder) (lookup : U32 → Option U8) :
    Preserves input (Mavlink.frameOutcome input order lookup) := by
  intro start next packet _ h
  have hp := Mavlink.frame_success input order lookup start next packet h
  refine ⟨hp.2.2.1, ?_⟩
  simp only [Spec.position, hp.1, hp.2.1, hp.2.2.2.1]
  omega

end RustHammer.Forward
