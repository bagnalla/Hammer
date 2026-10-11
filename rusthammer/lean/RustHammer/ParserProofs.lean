import RustHammer.ControlProofs
import RustHammer.ControlSpec

open RustHammer.Code.grammar.bytes
  RustHammer.Code.grammar.control
  RustHammer.Code.grammar.numeric
  RustHammer.Code.grammar.position
  RustHammer.Code.grammar.sequence
  RustHammer.Code.grammar.transform
  RustHammer.Code.input_types

open Aeneas Aeneas.Std Result WP

namespace RustHammer.Proofs
open Code

theorem bit_with_spec (input : Slice U8) (cursor : Cursor) :
    Bit.Insts.RusthammerParser_traitsParserInputBool.parse_with () input cursor ByteOrder.Big
      ⦃ result => Spec.bitOutcome input cursor result ⦄ := by
  exact bit_spec input cursor

theorem bits_with_spec (parser : Bits) (input : Slice U8) (cursor : Cursor)
    (hconfig : Spec.validBits parser) :
    Bits.Insts.RusthammerParser_traitsParserInputU64.parse_with parser input cursor ByteOrder.Big
      ⦃ result => Spec.bitsOutcome input cursor parser.width result ⦄ := by
  exact bits_spec parser input cursor hconfig

theorem take_aligned_with_spec (parser : TakeAligned) (input : Slice U8) (cursor : Cursor) :
    TakeAligned.Insts.RusthammerParser_traitsParserInputSharedInputSliceU8.parse_with parser input cursor ByteOrder.Big
      ⦃ result => Spec.takeAlignedOutcome input cursor parser.count result ⦄ := by
  exact take_aligned_parser_spec parser input cursor

theorem literal_with_spec (parser : Literal) (input : Slice U8) (cursor : Cursor) (hconfig : Spec.validLiteral parser) :
    Literal.Insts.RusthammerParser_traitsParserInputU64.parse_with parser input cursor ByteOrder.Big
      ⦃ result => Spec.literalOutcome input cursor parser.bits.width parser.value result ⦄ := by
  exact literal_spec parser input cursor hconfig

/-- End rejects all remaining bits and malformed cursors, without consuming input. -/
theorem end_with_spec (input : Slice U8) (cursor : Cursor) :
    End.Insts.RusthammerParser_traitsParserInputTuple.parse_with () input cursor ByteOrder.Big
      ⦃ result => Spec.endOutcome input cursor result ⦄ := by
  simpa only [Spec.endOutcome] using end_spec input cursor

/-- A child error bypasses the mapping callback. -/
theorem map_child_error {P F α β : Type} (pi : parser_traits.Parser P α) (fi : core.ops.function.Fn F α β)
    (parser : Map P F) (context : ByteOrder) (input : Slice U8) (cursor : Cursor) (error : ParseError)
    (hp : pi.parse_with parser.parser input cursor context ⦃ result => result = .Err error ⦄) :
    Map.Insts.RusthammerParser_traitsParser.parse_with pi fi parser input cursor context
      ⦃ result => result = .Err error ⦄ := by
  rw [Map.Insts.RusthammerParser_traitsParser.parse_with]
  step with hp as ⟨parsed, hparsed⟩
  simp [hparsed, spec_ok]

theorem verify_child_error {P F α : Type} (pi : parser_traits.Parser P α)
    (fi : core.ops.function.Fn F α Bool) (parser : Verify P F)
    (context : ByteOrder) (input : Slice U8) (cursor : Cursor) (error : ParseError)
    (hp : pi.parse_with parser.parser input cursor context ⦃ result => result = .Err error ⦄) :
    Verify.Insts.RusthammerParser_traitsParser.parse_with pi fi parser input cursor context
      ⦃ result => result = .Err error ⦄ := by
  rw [Verify.Insts.RusthammerParser_traitsParser.parse_with]
  step with hp as ⟨parsed, hparsed⟩
  simp [hparsed, spec_ok]

theorem choice_first_success {P Q α : Type} (pi : parser_traits.Parser P α) (qi : parser_traits.Parser Q α)
    (parser : Choice P Q) (context : ByteOrder) (input : Slice U8) (cursor next : Cursor) (value : α)
    (hp : pi.parse_with parser.first input cursor context ⦃ result => result = .Ok (next, value) ⦄) :
    Choice.Insts.RusthammerParser_traitsParser.parse_with pi qi parser input cursor context
      ⦃ result => result = .Ok (next, value) ⦄ := by
  rw [Choice.Insts.RusthammerParser_traitsParser.parse_with]
  step with hp as ⟨left, hleft⟩
  simp [hleft, spec_ok]

theorem choice_first_fatal {P Q α : Type} (pi : parser_traits.Parser P α) (qi : parser_traits.Parser Q α)
    (parser : Choice P Q) (context : ByteOrder) (input : Slice U8) (cursor : Cursor) (error : ParseError)
    (hfatal : ¬Spec.recoverable error)
    (hp : pi.parse_with parser.first input cursor context ⦃ result => result = .Err error ⦄) :
    Choice.Insts.RusthammerParser_traitsParser.parse_with pi qi parser input cursor context
      ⦃ result => result = .Err error ⦄ := by
  rw [Choice.Insts.RusthammerParser_traitsParser.parse_with]
  step with hp as ⟨left, hleft⟩
  simp only [hleft]
  step with recoverable_spec error as ⟨retry, hretry⟩
  have hfalse : retry = false := by simpa [hfatal] using hretry
  simp [hfalse, spec_ok]

end RustHammer.Proofs

namespace RustHammer.Ordering
open Code Proofs

theorem bit_with_spec (input : Slice U8) (cursor : Cursor) (context : ByteOrder) :
    Bit.Insts.RusthammerParser_traitsParserInputBool.parse_with () input cursor context
      ⦃ result => bitOutcome input cursor result ⦄ := by
  exact Proofs.bit_with_spec input cursor

/-- These primitives depend only on the input position, regardless of byte order. -/
theorem take_aligned_with_spec (parser : TakeAligned) (input : Slice U8) (cursor : Cursor)
    (context : ByteOrder) :
    TakeAligned.Insts.RusthammerParser_traitsParserInputSharedInputSliceU8.parse_with parser input cursor context
      ⦃ result => Spec.takeAlignedOutcome input cursor parser.count result ⦄ := by
  exact Proofs.take_aligned_with_spec parser input cursor

theorem end_with_spec (input : Slice U8) (cursor : Cursor) (context : ByteOrder) :
    End.Insts.RusthammerParser_traitsParserInputTuple.parse_with () input cursor context
      ⦃ result => Spec.endOutcome input cursor  result ⦄ := by
  exact Proofs.end_with_spec input cursor

end RustHammer.Ordering
