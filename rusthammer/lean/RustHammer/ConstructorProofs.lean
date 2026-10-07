import RustHammer.BackendProofs

open Aeneas Aeneas.Std Result WP

namespace RustHammer.Constructors
open Code

/-! Construction preserves the exact stored children and callbacks. These
equations establish totality without assumptions about child interpretation or
callback termination: neither operation is invoked by a constructor. The existing
node specifications govern parsing; `reuse_spec` transports any such contract
through construction, for any backend, context, output, or parsing entry point. -/

@[simp] theorem seq_eq {P Q : Type} (first : P) (second : Q) :
    Code.seq first second = ok (Code.Seq.mk first second) := rfl

@[simp] theorem choice_eq {P Q α : Type} (pi : Grammar P α) (qi : Grammar Q α)
    (first : P) (second : Q) :
    Code.choice pi qi first second = ok (Code.Choice.mk first second) := rfl

@[simp] theorem optional_eq {P : Type} (parser : P) :
    Code.optional parser = ok (Code.Optional.mk parser) := rfl

@[simp] theorem map_eq {P F α β : Type} (pi : Grammar P α)
    (fi : core.ops.function.Fn F α β) (parser : P) (mapping : F) :
    Code.map pi fi parser mapping = ok (Code.Map.mk parser mapping) := rfl

@[simp] theorem try_map_eq {P F α β ε : Type} (pi : Grammar P α)
    (fi : core.ops.function.Fn F α (core.result.Result β ε)) (parser : P) (mapping : F) :
    Code.try_map pi fi parser mapping = ok (Code.TryMap.mk parser mapping) := rfl

@[simp] theorem verify_eq {P F α : Type} (pi : Grammar P α)
    (fi : core.ops.function.Fn F α Bool) (parser : P) (predicate : F) :
    Code.verify pi fi parser predicate = ok (Code.Verify.mk parser predicate) := rfl

@[simp] theorem bind_eq {P F Q α β : Type} (pi : Grammar P α)
    (fi : core.ops.function.Fn F α Q) (qi : Grammar Q β) (parser : P) (factory : F) :
    Code.bind pi fi qi parser factory = ok (Code.Bind.mk parser factory) := rfl

/-- Every property of evaluating a node also holds after constructing that node.
The continuation may invoke Eval with mutable backend state, either default
Parser method, or another grammar constructor. -/
theorem reuse_spec {G α : Type} (constructor : Result G) (node : G)
    (hconstructor : constructor = ok node) (run : G → Result α) (post : α → Prop)
    (hrun : run node ⦃ result => post result ⦄) :
    (do let parser ← constructor; run parser) ⦃ result => post result ⦄ := by
  simpa only [hconstructor, bind_ok] using hrun

/-- Example of reusing the existing stateful sequencing contract. No parsing
implementation or independent sequencing semantics is added for the helper. -/
theorem seq_eval_spec {State P Q α β : Type} (pi : Eval P State α) (qi : Eval Q State β)
    (first : P) (second : Q) (state : State) (input : Slice U8) (cursor : Cursor) (ctx : ParseContext)
    (left : Backend.Contract State α) (right : Backend.Contract State β)
    (hp : pi.eval first state input cursor ctx ⦃ result => left state cursor result ⦄)
    (hq : ∀ next value middle, left state cursor (.Success next value, middle) →
      qi.eval second middle input next ctx ⦃ result => right middle next result ⦄) :
    (do let parser ← Code.seq first second
        Seq.Insts.RusthammerEvalInputBackendPair.eval pi qi parser state input cursor ctx)
      ⦃ result => Backend.sequence left right state cursor result ⦄ := by
  apply reuse_spec (Code.seq first second) (Code.Seq.mk first second) (seq_eq first second)
  exact Backend.seq_eval_spec pi qi ⟨first, second⟩ state input cursor ctx left right hp hq

end RustHammer.Constructors
