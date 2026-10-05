import RustHammer.CompleteProofs
import RustHammer.ControlSpec

open Aeneas Aeneas.Std Result WP

namespace RustHammer.Proofs
open Code
open marker_example

theorem recoverable_spec (error : ParseError) :
    ParseError.is_recoverable error ⦃ result => result = decide (Spec.recoverable error) ⦄ := by
  cases error <;> simp [ParseError.is_recoverable, Spec.recoverable, spec_ok]

/-- End rejects all remaining bits and malformed cursors, without consuming input. -/
theorem end_spec (input : Slice U8) (cursor : Cursor) :
    End.Insts.RusthammerParserInputTuple.parse_with () input cursor .Final
      ⦃ result => Spec.completed (Spec.endOutcome input cursor) result ⦄ := by
  unfold Spec.completed
  by_cases hvalid : Spec.validCursor input cursor
  · have hparts := hvalid
    unfold Spec.validCursor Spec.position at hparts
    have hbit : ¬cursor.bit ≥ 8#u8 := by scalar_tac
    have hbyte : ¬cursor.byte > input.len := by scalar_tac
    simp only [Spec.endOutcome, if_pos hvalid,
      End.Insts.RusthammerParserInputTuple.parse_with, hbit, hbyte, ↓reduceIte]
    by_cases heq : cursor.byte = input.len
    · have hzero : cursor.bit = 0#u8 := by scalar_tac
      have hend : Spec.position cursor = 8 * input.val.length := by
        unfold Spec.position
        scalar_tac
      simp [heq, hzero, hend, spec_ok, Spec.completedResult]
    · have hnotend : ¬Spec.position cursor = 8 * input.val.length := by
        unfold Spec.position
        scalar_tac
      simp [heq, hnotend, spec_ok, Spec.completedResult]
  · have hparts := hvalid
    unfold Spec.validCursor Spec.position at hparts
    simp only [Spec.endOutcome, if_neg hvalid]
    by_cases hbit : cursor.bit ≥ 8#u8
    · simp [End.Insts.RusthammerParserInputTuple.parse_with, hbit, spec_ok, Spec.completedResult]
    · by_cases hbyte : cursor.byte > input.len
      · simp [End.Insts.RusthammerParserInputTuple.parse_with, hbit, hbyte, spec_ok, Spec.completedResult]
      · have heq : cursor.byte = input.len := by scalar_tac
        have hnonzero : cursor.bit ≠ 0#u8 := by scalar_tac
        simp [End.Insts.RusthammerParserInputTuple.parse_with, hbit, heq, hnonzero, spec_ok, Spec.completedResult]

/-- Construction validates the width and then the literal's representability. -/
theorem literal_new_spec (width : U8) (value : U64) :
    Literal.new width value ⦃ result => Spec.literalNewOutcome width value result ⦄ := by
  unfold Literal.new
  step with bits_new_spec width as ⟨bits, hbits⟩
  by_cases hwidth : width.val ≤ 64
  · simp only [Spec.bitsNewOutcome, if_pos hwidth] at hbits
    simp only [hbits, Spec.literalNewOutcome, if_pos hwidth]
    by_cases hsmall : width < 64#u8
    · have hsmallNat : width.val < 64 := by scalar_tac
      simp only [hsmall, ↓reduceIte]
      step as ⟨limit, hlimit, hlimitBv⟩
      have hpow : 2 ^ width.val < U64.size := by
        simp only [U64.size, U64.numBits]
        exact Nat.pow_lt_pow_right (by omega) hsmallNat
      have hlimitValue : limit.val = 2 ^ width.val := by
        simpa [Nat.one_shiftLeft, Nat.mod_eq_of_lt hpow] using hlimit
      by_cases hfit : value.val < 2 ^ width.val
      · have hbelow : ¬value ≥ limit := by scalar_tac
        simp [hbelow, hfit, spec_ok]
      · have habove : value ≥ limit := by scalar_tac
        simp [habove, hfit, spec_ok]
    · have hfull : width.val = 64 := by scalar_tac
      have hfit : value.val < 2 ^ width.val := by
        rw [hfull]
        scalar_tac
      simp [hsmall, hfit, spec_ok]
  · simp only [Spec.bitsNewOutcome, if_neg hwidth] at hbits
    simp [hbits, Spec.literalNewOutcome, hwidth, spec_ok]

/-- Successful literal construction establishes both configuration invariants. -/
theorem literal_new_valid (width : U8) (value : U64) (parser : Literal)
    (hnew : Literal.new width value = ok (.Ok parser)) : Spec.validLiteral parser := by
  have hspec := literal_new_spec width value
  rw [hnew] at hspec
  simp only [spec_ok, Spec.literalNewOutcome] at hspec
  split at hspec
  · split at hspec
    · cases hspec
      exact ⟨by assumption, by assumption⟩
    · cases hspec
  · cases hspec

theorem literal_width_spec (parser : Literal) :
    Literal.width parser ⦃ result => result = parser.bits.width ⦄ := by
  exact bits_width_spec parser.bits

theorem literal_value_spec (parser : Literal) :
    Literal.impl.value parser ⦃ result => result = parser.value ⦄ := by
  simp [Literal.impl.value, spec_ok]

/-- Validated literal matching refines numeric decoding, including every input error. -/
theorem literal_decode_spec (parser : Literal) (input : Slice U8) (cursor : Cursor)
    (hconfig : Spec.validLiteral parser) :
    read_literal input cursor parser
      ⦃ result => Spec.literalOutcome input cursor parser.bits.width parser.value result ⦄ := by
  unfold read_literal Spec.literalOutcome
  step with read_bits_spec input cursor parser.bits hconfig.1 as ⟨numeric, hnumeric⟩
  cases numeric with
  | Err error =>
    simp only [spec_ok]
    exact ⟨.Err error, hnumeric, rfl⟩
  | Ok pair =>
    rcases pair with ⟨next, value⟩
    change ((if value = parser.value then ok (.Ok (next, value))
      else ok (.Err ParseError.Mismatch)) : Result (Spec.ParseResult U64))
      ⦃ result => ∃ numeric, Spec.bitsOutcome input cursor parser.bits.width numeric ∧
        result = Spec.literalResult parser.value numeric ⦄
    by_cases heq : value = parser.value
    · simp only [heq, ↓reduceIte, spec_ok]
      exact ⟨.Ok (next, value), hnumeric, by simp [Spec.literalResult, heq]⟩
    · have hneNat : value.val ≠ parser.value.val := by scalar_tac
      simp only [heq, ↓reduceIte, spec_ok]
      exact ⟨.Ok (next, value), hnumeric, by simp [Spec.literalResult, hneNat]⟩

theorem literal_spec (parser : Literal) (input : Slice U8) (cursor : Cursor)
    (hconfig : Spec.validLiteral parser) :
    Literal.Insts.RusthammerParserInputU64.parse_with parser input cursor .Final
      ⦃ result => Spec.completed (Spec.literalOutcome input cursor parser.bits.width parser.value) result ⦄ := by
  unfold Literal.Insts.RusthammerParserInputU64.parse_with
  step with literal_decode_spec parser input cursor hconfig as ⟨result, hresult⟩
  step with classify_final_spec result as ⟨outcome, houtcome⟩
  exact ⟨result, hresult, houtcome⟩

/-- Ordered choice preserves its children's contracts and restarts at the original cursor. -/
theorem choice_spec {P Q α : Type} (pi : Parser P α) (qi : Parser Q α)
    (parser : Choice P Q) (input : Slice U8) (cursor : Cursor)
    (first second : Cursor → Spec.ParseResult α → Prop)
    (hp : ∀ start, pi.parse_with parser.first input start .Final ⦃ result => Spec.completed (first start) result ⦄)
    (hq : ∀ start, qi.parse_with parser.second input start .Final ⦃ result => Spec.completed (second start) result ⦄) :
    Choice.Insts.RusthammerParser.parse_with pi qi parser input cursor .Final
      ⦃ result => Spec.completed (Spec.choice first second cursor) result ⦄ := by
  unfold Choice.Insts.RusthammerParser.parse_with
  step with hp cursor as ⟨outcome, houtcome⟩
  rcases houtcome with ⟨left, hleft, rfl⟩
  cases left with
  | Ok pair =>
    rcases pair with ⟨next, value⟩
    simp only [spec_ok, Spec.completedResult, Spec.completed_success]
    exact ⟨.Ok (next, value), hleft, rfl⟩
  | Err error =>
    simp only [Spec.completedResult]
    step with recoverable_spec error as ⟨retry, hretry⟩
    by_cases hrecover : Spec.recoverable error
    · have htrue : retry = true := by simpa [hrecover] using hretry
      simp only [htrue, ↓reduceIte]
      step with hq cursor as ⟨outcome, houtcome⟩
      rcases houtcome with ⟨right, hright, rfl⟩
      simp only [Spec.completed_embed]
      refine ⟨.Err error, hleft, ?_⟩
      simpa only [if_pos hrecover] using hright
    · have hfalse : retry = false := by simpa [hrecover] using hretry
      simp only [hfalse, Bool.false_eq_true, ↓reduceIte, spec_ok, Spec.completed_error]
      exact ⟨.Err error, hleft, by simp [hrecover]⟩

/-- An absent optional value consumes nothing. -/
theorem optional_absent_cursor {α : Type} (child : Cursor → Spec.ParseResult α → Prop)
    (cursor next : Cursor) (h : Spec.optional child cursor (.Ok (next, none))) :
    next = cursor := by
  rcases h with ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩
  · cases h
  · cases h
    rfl
  · cases h

/-- Successful positive lookahead consumes nothing. -/
theorem and_success_cursor {α : Type} (child : Cursor → Spec.ParseResult α → Prop)
    (cursor next : Cursor) (h : Spec.and child cursor (.Ok (next, ()))) :
    next = cursor := by
  rcases h with ⟨_, _, _, h⟩ | ⟨_, _, h⟩
  · cases h
    rfl
  · cases h

/-- Successful negative lookahead consumes nothing. -/
theorem not_success_cursor {α : Type} (child : Cursor → Spec.ParseResult α → Prop)
    (cursor next : Cursor) (h : Spec.not child cursor (.Ok (next, ()))) :
    next = cursor := by
  rcases h with ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩
  · cases h
    rfl
  · cases h
  · cases h

/-- The example's fallible constructor always produces the intended fixed grammar. -/
theorem marker_new_spec :
    Marker.new ⦃ result => result = .Ok { parser := Spec.markerParser } ⦄ := by
  unfold Marker.new
  step with literal_new_spec 16#u8 51966#u64 as ⟨first, hfirst⟩
  simp [Spec.literalNewOutcome] at hfirst
  simp only [hfirst]
  step with literal_new_spec 8#u8 202#u64 as ⟨second, hsecond⟩
  simp [Spec.literalNewOutcome] at hsecond
  simp [hsecond, Spec.markerParser, spec_ok]

theorem marker_new_valid (parser : Marker)
    (hnew : Marker.new = ok (.Ok parser)) : Spec.validMarker parser := by
  have hspec := marker_new_spec
  rw [hnew] at hspec
  simp only [spec_ok, core.result.Result.Ok.injEq] at hspec
  cases hspec
  rfl

/-- The constructed example implements its ordered grammar for every input and cursor. -/
theorem marker_parser_spec (parser : Marker) (input : Slice U8) (cursor : Cursor)
    (hconfig : Spec.validMarker parser) :
    Marker.Insts.RusthammerParserInputU64.parse_with parser input cursor .Final
      ⦃ result => Spec.completed (Spec.markerOutcome input cursor) result ⦄ := by
  let li := Literal.Insts.RusthammerParserInputU64
  let ci := Choice.Insts.RusthammerParser li li
  let alternatives : Choice Literal Literal := Spec.markerParser.first
  have hchoice (start : Cursor) := choice_spec li li alternatives input start
    (fun start => Spec.literalOutcome input start 16#u8 51966#u64)
    (fun start => Spec.literalOutcome input start 8#u8 202#u64)
    (fun start => literal_spec _ input start (by decide))
    (fun start => literal_spec _ input start (by decide))
  unfold Marker.Insts.RusthammerParserInputU64.parse_with
  rw [hconfig]
  step with seq_spec ci End.Insts.RusthammerParserInputTuple
    { first := alternatives, second := () } input cursor
    (Spec.choice (fun start => Spec.literalOutcome input start 16#u8 51966#u64)
      (fun start => Spec.literalOutcome input start 8#u8 202#u64))
    (Spec.endOutcome input) hchoice (end_spec input) as ⟨outcome, houtcome⟩
  rcases houtcome with ⟨fields, hfields, rfl⟩
  cases fields with
  | Err error =>
    simp only [Spec.completedResult, spec_ok, Spec.completed_error]
    exact ⟨.Err error, hfields, rfl⟩
  | Ok pair =>
    rcases pair with ⟨next, value, empty⟩
    cases empty
    change (ok (.Success next value) : Result (ParseOutcome U64))
      ⦃ result => Spec.completed (Spec.markerOutcome input cursor) result ⦄
    simp only [spec_ok, Spec.completed_success]
    exact ⟨.Ok (next, (value, ())), hfields, rfl⟩

/-- The convenience function accepts an already constructed marker parser. -/
theorem marker_spec (input : Slice U8) (cursor : Cursor) (parser : Marker)
    (hconfig : Spec.validMarker parser) :
    parse_marker input cursor parser ⦃ result => Spec.markerOutcome input cursor result ⦄ := by
  exact complete_spec Marker.Insts.RusthammerParserInputU64 parser input cursor
    (Spec.markerOutcome input cursor) (marker_parser_spec parser input cursor hconfig)

/-- Optionality is a total transformation of the child's contract, including absent
values after partial rejection and successful values that borrow from the input. -/
theorem optional_spec {P α : Type} (pi : Parser P α) (parser : Optional P)
    (input : Slice U8) (cursor : Cursor) (child : Cursor → Spec.ParseResult α → Prop)
    (hp : pi.parse_with parser.parser input cursor .Final
      ⦃ result => Spec.completed (child cursor) result ⦄) :
    Optional.Insts.RusthammerParserInputOption.parse_with pi parser input cursor .Final
      ⦃ result => Spec.completed (Spec.optional child cursor) result ⦄ := by
  unfold Optional.Insts.RusthammerParserInputOption.parse_with
  step with hp as ⟨outcome, houtcome⟩
  rcases houtcome with ⟨parsed, hparsed, rfl⟩
  cases parsed with
  | Ok pair =>
    rcases pair with ⟨next, value⟩
    change (ok (.Success next (some value)) : Result (ParseOutcome (Option α)))
      ⦃ result => Spec.completed (Spec.optional child cursor) result ⦄
    simp only [spec_ok, Spec.completed_success]
    exact Or.inl ⟨next, value, hparsed, rfl⟩
  | Err error =>
    simp only [Spec.completedResult]
    step with recoverable_spec error as ⟨recover, hrecover⟩
    by_cases h : Spec.recoverable error
    · have htrue : recover = true := by simpa [h] using hrecover
      simp only [htrue, ↓reduceIte, spec_ok, Spec.completed_success]
      exact Or.inr (Or.inl ⟨error, hparsed, h, rfl⟩)
    · have hfalse : recover = false := by simpa [h] using hrecover
      simp only [hfalse, Bool.false_eq_true, ↓reduceIte, spec_ok, Spec.completed_error]
      exact Or.inr (Or.inr ⟨error, hparsed, h, rfl⟩)

/-- Positive lookahead preserves every error and restores the cursor on success,
regardless of the child's output type or how far it advanced. -/
theorem and_spec {P α : Type} (pi : Parser P α) (parser : Code.And P)
    (input : Slice U8) (cursor : Cursor) (child : Cursor → Spec.ParseResult α → Prop)
    (hp : pi.parse_with parser.parser input cursor .Final
      ⦃ result => Spec.completed (child cursor) result ⦄) :
    Code.And.Insts.RusthammerParserInputTuple.parse_with pi parser input cursor .Final
      ⦃ result => Spec.completed (Spec.and child cursor) result ⦄ := by
  unfold Code.And.Insts.RusthammerParserInputTuple.parse_with
  step with hp as ⟨outcome, houtcome⟩
  rcases houtcome with ⟨parsed, hparsed, rfl⟩
  cases parsed with
  | Ok pair =>
    rcases pair with ⟨next, value⟩
    simp only [Spec.completedResult, spec_ok, Spec.completed_success]
    exact Or.inl ⟨next, value, hparsed, rfl⟩
  | Err error =>
    simp only [Spec.completedResult, spec_ok, Spec.completed_error]
    exact Or.inr ⟨error, hparsed, rfl⟩

/-- Negative lookahead reverses match/rejection while preserving fatal errors.
No progress assumption is needed for a child that succeeds without consuming input. -/
theorem not_spec {P α : Type} (pi : Parser P α) (parser : Code.Not P)
    (input : Slice U8) (cursor : Cursor) (child : Cursor → Spec.ParseResult α → Prop)
    (hp : pi.parse_with parser.parser input cursor .Final
      ⦃ result => Spec.completed (child cursor) result ⦄) :
    Code.Not.Insts.RusthammerParserInputTuple.parse_with pi parser input cursor .Final
      ⦃ result => Spec.completed (Spec.not child cursor) result ⦄ := by
  unfold Code.Not.Insts.RusthammerParserInputTuple.parse_with
  step with hp as ⟨outcome, houtcome⟩
  rcases houtcome with ⟨parsed, hparsed, rfl⟩
  cases parsed with
  | Ok pair =>
    rcases pair with ⟨next, value⟩
    simp only [Spec.completedResult, spec_ok, Spec.completed_error]
    exact Or.inr (Or.inl ⟨next, value, hparsed, rfl⟩)
  | Err error =>
    simp only [Spec.completedResult]
    step with recoverable_spec error as ⟨recover, hrecover⟩
    by_cases h : Spec.recoverable error
    · have htrue : recover = true := by simpa [h] using hrecover
      simp only [htrue, ↓reduceIte, spec_ok, Spec.completed_success]
      exact Or.inl ⟨error, hparsed, h, rfl⟩
    · have hfalse : recover = false := by simpa [h] using hrecover
      simp only [hfalse, Bool.false_eq_true, ↓reduceIte, spec_ok, Spec.completed_error]
      exact Or.inr (Or.inr ⟨error, hparsed, h, rfl⟩)

end RustHammer.Proofs
