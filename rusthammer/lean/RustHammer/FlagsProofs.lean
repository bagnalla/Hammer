import RustHammer.CompleteProofs

open Aeneas Aeneas.Std Result WP

namespace RustHammer.Proofs
open Code
open flags_example

/-- The typed example refines its three-bit grammar, including every error path. -/
theorem flags_spec (input : Slice U8) (cursor : Cursor) :
    parse_flags input cursor ⦃ result => Spec.flagsOutcome input cursor result ⦄ := by
  let bi := Bit.Insts.RusthammerParserInputBool
  let pair := Seq.Insts.RusthammerParserInputPair bi bi
  have hbit := bit_spec input
  have hpair (start : Cursor) :=
    seq_spec bi bi { first := (), second := () } input start
      (Spec.bitOutcome input) (Spec.bitOutcome input) hbit hbit
  have hfields := seq_spec bi pair { first := (), second := { first := (), second := () } }
    input cursor (Spec.bitOutcome input)
    (Spec.sequence (Spec.bitOutcome input) (Spec.bitOutcome input)) hbit hpair
  let fi := parse_flags.closure.Insts.CoreOpsFunctionFnTuplePairBoolPairBoolBoolFlags
  let mapping := fun (fields : Bool × (Bool × Bool)) (result : Flags) =>
    result = { urgent := fields.1, encrypted := fields.2.1, compressed := fields.2.2 }
  have hf (next : Cursor) (fields : Bool × (Bool × Bool))
      (_ : Spec.sequence (Spec.bitOutcome input)
        (Spec.sequence (Spec.bitOutcome input) (Spec.bitOutcome input)) cursor (.Ok (next, fields))) :
      fi.call () fields ⦃ result => mapping fields result ⦄ := by
    rcases fields with ⟨urgent, encrypted, compressed⟩
    simp [fi, mapping,
      parse_flags.closure.Insts.CoreOpsFunctionFnTuplePairBoolPairBoolBoolFlags.call, spec_ok]
  let parser : Map (Seq Unit (Seq Unit Unit)) Unit :=
    { parser := { first := (), second := { first := (), second := () } }, map := () }
  let mi := Map.Insts.RusthammerParser (Seq.Insts.RusthammerParserInputPair bi pair) fi
  have hfinal : mi.parse_with parser input cursor ParseContext.FINAL
      ⦃ result => Spec.completed (Spec.flagsOutcome input cursor) result ⦄ := by
    change Map.Insts.RusthammerParser.parse_with
      (Seq.Insts.RusthammerParserInputPair bi pair) fi parser input cursor ParseContext.FINAL
        ⦃ result => Spec.completed (Spec.flagsOutcome input cursor) result ⦄
    step with map_spec (Seq.Insts.RusthammerParserInputPair bi pair) fi parser
      input cursor (Spec.sequence (Spec.bitOutcome input)
        (Spec.sequence (Spec.bitOutcome input) (Spec.bitOutcome input))) mapping hfields hf
      as ⟨outcome, houtcome⟩
    rcases houtcome with ⟨result, hresult, rfl⟩
    simp only [Spec.completed_embed]
    rcases hresult with ⟨fields, hfields, hmapped⟩
    cases fields with
    | Err error =>
      exact ⟨.Err error, hfields, hmapped⟩
    | Ok values =>
      rcases values with ⟨next, urgent, encrypted, compressed⟩
      rcases hmapped with ⟨mapped, rfl, hresult⟩
      exact ⟨.Ok (next, (urgent, (encrypted, compressed))), hfields, hresult⟩

  exact complete_spec mi parser input cursor (Spec.flagsOutcome input cursor) hfinal

end RustHammer.Proofs
