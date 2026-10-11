import RustHammer.ParserProofs

open RustHammer.Code.grammar.sequence
  RustHammer.Code.input_types
  RustHammer.Code.parser_traits

open Aeneas Aeneas.Std Result WP

namespace RustHammer.Constructors
open Code

/-! Construction preserves the exact stored children and callbacks. These
equations establish totality without assumptions about child interpretation or
callback termination: neither operation is invoked by a constructor. The existing
node specifications govern parsing; `reuse_spec` transports any such contract
through construction, for any byte order, output, or parsing entry point. -/

@[simp] theorem seq_eq {P Q : Type} (first : P) (second : Q) :
    Code.grammar.sequence.seq first second = ok (Code.grammar.sequence.Seq.mk first second) := rfl

@[simp] theorem choice_eq {P Q α : Type} (pi : Parser P α) (qi : Parser Q α)
    (first : P) (second : Q) :
    Code.grammar.control.choice pi qi first second = ok (Code.grammar.control.Choice.mk first second) := rfl

@[simp] theorem optional_eq {P : Type} (parser : P) :
    Code.grammar.control.optional parser = ok (Code.grammar.control.Optional.mk parser) := rfl

@[simp] theorem map_eq {P F α β : Type} (pi : Parser P α)
    (fi : core.ops.function.Fn F α β) (parser : P) (mapping : F) :
    Code.grammar.transform.map pi fi parser mapping = ok (Code.grammar.transform.Map.mk parser mapping) := rfl

@[simp] theorem try_map_eq {P F α β ε : Type} (pi : Parser P α)
    (fi : core.ops.function.Fn F α (core.result.Result β ε)) (parser : P) (mapping : F) :
    Code.grammar.transform.try_map pi fi parser mapping = ok (Code.grammar.transform.TryMap.mk parser mapping) := rfl

@[simp] theorem verify_eq {P F α : Type} (pi : Parser P α)
    (fi : core.ops.function.Fn F α Bool) (parser : P) (predicate : F) :
    Code.grammar.transform.verify pi fi parser predicate = ok (Code.grammar.transform.Verify.mk parser predicate) := rfl

@[simp] theorem bind_eq {P F Q α β : Type} (pi : Parser P α)
    (fi : core.ops.function.Fn F α Q) (qi : Parser Q β) (parser : P) (factory : F) :
    Code.grammar.sequence.bind pi fi qi parser factory = ok (Code.grammar.sequence.Bind.mk parser factory) := rfl

/-- Every property of evaluating a node also holds after constructing that node.
The continuation may invoke a parser or another grammar constructor. -/
theorem reuse_spec {G α : Type} (constructor : Result G) (node : G)
    (hconstructor : constructor = ok node) (run : G → Result α) (post : α → Prop)
    (hrun : run node ⦃ result => post result ⦄) :
    (do let parser ← constructor; run parser) ⦃ result => post result ⦄ := by
  simpa only [hconstructor, bind_ok] using hrun

/-- Sequencing after construction has the same child contracts as a stored node. -/
theorem seq_parse_spec {P Q α β : Type} (pi : Parser P α) (qi : Parser Q β)
    (first : P) (second : Q) (input : Slice U8) (cursor : Cursor) (order : ByteOrder)
    (left : Cursor → Spec.ParseResult α → Prop)
    (right : Cursor → Spec.ParseResult β → Prop)
    (hp : ∀ start, pi.parse_with first input start order ⦃ result => left start result ⦄)
    (hq : ∀ start, qi.parse_with second input start order ⦃ result => right start result ⦄) :
    (do let parser ← Code.grammar.sequence.seq first second
        Seq.Insts.RusthammerParser_traitsParserInputPair.parse_with pi qi parser input cursor order)
      ⦃ result => Contracts.sequence left right cursor result ⦄ := by
  apply reuse_spec (Code.grammar.sequence.seq first second)
    (Code.grammar.sequence.Seq.mk first second) (seq_eq first second)
  exact Proofs.seq_with_spec pi qi ⟨first, second⟩ input cursor order left right hp hq

end RustHammer.Constructors
