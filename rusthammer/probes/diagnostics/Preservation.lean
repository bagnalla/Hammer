/- Appended to each freshly extracted probe module by check_diagnostics.py.
   All implementation definitions below come from Rust, including the collector.
   The abstract hook/child obligations are hypotheses, not project axioms. -/

namespace DiagnosticProbe.Preservation
open Aeneas Aeneas.Std Result
open rusthammer.input_types rusthammer.parser_traits rusthammer.grammar.numeric

abbrev Total {α : Type} (computation : Result α) : Prop := ∃ value, computation = .ok value

structure HooksTotal {O M : Type} (hooks : Observe O M) : Prop where
  begin : ∀ observer, Total (hooks.begin observer)
  finish : ∀ observer mark keep, Total (hooks.finish observer mark keep)
  record : ∀ observer failure, Total (hooks.record observer failure)
  fallback : ∀ observer cursor issue, Total (hooks.fallback observer cursor issue)
  annotate : ∀ observer label, Total (hooks.annotate observer label)

theorem priority_total (issue : Issue) : Total (priority issue) := by
  cases issue with
  | Incomplete => exact ⟨_, rfl⟩
  | Rejected error => cases error <;> simp [priority, ParseError.is_recoverable, Total]

theorem failure_annotate_total (failure : Failure) (label : Label) :
    Total (Failure.annotate failure label) := by
  unfold Failure.annotate
  dsimp only
  split <;> first | exact ⟨_, rfl⟩ | (split <;> exact ⟨_, rfl⟩)

theorem insert_total (report : Report) (failure : Failure) :
    Total (Report.insert report failure) := by
  unfold Report.insert
  split
  · exact ⟨_, rfl⟩
  · rename_i current _
    obtain ⟨old, ho⟩ := priority_total current.issue
    obtain ⟨new, hn⟩ := priority_total failure.issue
    simp only [ho, hn, bind_ok]
    split <;> (try split) <;> simp only [bind_ok]
    all_goals repeat' first | (exact ⟨_, rfl⟩) | split

theorem merge_total (report other : Report) : Total (Report.merge report other) := by
  unfold Report.merge
  split
  · exact ⟨_, rfl⟩
  · rename_i first _
    obtain ⟨middle, hm⟩ := insert_total report first
    simp only [hm, bind_ok]
    have ht : Total (match other.second with
      | none => .ok (middle.first, middle.second, middle.alternatives_truncated)
      | some second => do
        let final ← Report.insert middle second
        .ok (final.first, final.second, final.alternatives_truncated)) := by
      split
      · exact ⟨_, rfl⟩
      · rename_i second _
        obtain ⟨final, hf⟩ := insert_total middle second
        simp [hf, Total]
    obtain ⟨⟨selected, rest, truncated⟩, hs⟩ := ht
    rw [hs]
    simp only [bind_ok]
    cases selected with
    | none => exact ⟨_, rfl⟩
    | some chosen =>
      obtain ⟨p, hp⟩ := priority_total first.issue
      obtain ⟨q, hq⟩ := priority_total chosen.issue
      simp only [uncurry, hp, hq, bind_ok]
      repeat' first | (exact ⟨_, rfl⟩) | split

theorem annotate_total (report : Report) (label : Label) :
    Total (Report.annotate report label) := by
  unfold Report.annotate
  have ht : Total (match report.first with
    | none => .ok none
    | some f => do let first ← Failure.annotate f label; .ok (some first)) := by
    split
    · exact ⟨_, rfl⟩
    · rename_i first _
      obtain ⟨next, hn⟩ := failure_annotate_total first label
      simp [hn, Total]
  obtain ⟨first, hf⟩ := ht
  rw [hf]
  simp only [bind_ok]
  split
  · exact ⟨_, rfl⟩
  · rename_i second _
    obtain ⟨next, hn⟩ := failure_annotate_total second label
    simp [hn, Total]

abbrev collecting := Collect.Insts.Rusthammer_diagnostic_probeObserveMetaReport
abbrev silent := Silent.Insts.Rusthammer_diagnostic_probeObserveMetaBool

theorem collecting_total : HooksTotal collecting := by
  constructor
  · intro observer
    simp [Collect.Insts.Rusthammer_diagnostic_probeObserveMetaReport.begin, Report.empty, Total]
  · intro observer mark keep
    change Total (Collect.Insts.Rusthammer_diagnostic_probeObserveMetaReport.finish _ _ _)
    unfold Collect.Insts.Rusthammer_diagnostic_probeObserveMetaReport.finish
    split
    · obtain ⟨next, hn⟩ := merge_total mark observer.report
      simp [hn, Total]
    · exact ⟨_, rfl⟩
  · intro observer failure
    obtain ⟨next, hn⟩ := insert_total observer.report failure
    simp [Collect.Insts.Rusthammer_diagnostic_probeObserveMetaReport.record, hn, Total]
  · intro observer cursor issue
    change Total (Collect.Insts.Rusthammer_diagnostic_probeObserveMetaReport.fallback _ _ _)
    unfold Collect.Insts.Rusthammer_diagnostic_probeObserveMetaReport.fallback
    have ht : Total (match observer.report.first with
      | none => .ok (none, true)
      | some f => do
        let p ← priority f.issue
        let q ← priority issue
        .ok (observer.report.first, p < q)) := by
      split
      · exact ⟨_, rfl⟩
      · rename_i first _
        obtain ⟨p, hp⟩ := priority_total first.issue
        obtain ⟨q, hq⟩ := priority_total issue
        simp [hp, hq, Total]
    obtain ⟨⟨first, needed⟩, ht⟩ := ht
    rw [ht]
    simp only [bind_ok]
    cases needed with
    | false => exact ⟨_, rfl⟩
    | true =>
      obtain ⟨next, hn⟩ := insert_total { observer.report with first := first }
        ⟨cursor, false, issue, .Unspecified, none, none, false⟩
      simp [Failure.new, hn, Total]
  · intro observer label
    obtain ⟨next, hn⟩ := annotate_total observer.report label
    simp [Collect.Insts.Rusthammer_diagnostic_probeObserveMetaReport.annotate, hn, Total]

theorem silent_total : HooksTotal silent := by
  constructor <;> intros <;> exact ⟨_, rfl⟩

theorem close_preserves {B O M T : Type} (hooks : Observe O M) (ht : HooksTotal hooks)
    (session : Session B O) (mark : M) (result : ParseOutcome T) :
    ∃ observer, close hooks session mark result = .ok (result, { session with observer }) := by
  cases result with
  | Success next value =>
    obtain ⟨observer, ho⟩ := ht.finish session.observer mark false
    exact ⟨observer, by simp [close, ho]⟩
  | Error error | NeedMore =>
    obtain ⟨observer, ho⟩ := ht.finish session.observer mark true
    exact ⟨observer, by simp [close, ho]⟩

theorem decorate_preserves {B O M T : Type} (hooks : Observe O M) (ht : HooksTotal hooks)
    (session : Session B O) (cursor : Cursor) (label : Option Label) (result : ParseOutcome T) :
    ∃ observer, decorate hooks session cursor label result =
      .ok (result, { session with observer }) := by
  cases result with
  | Success next value => exact ⟨session.observer, by simp [decorate]⟩
  | Error error | NeedMore =>
    unfold decorate
    simp only [bind_ok]
    obtain ⟨middle, hm⟩ := ht.fallback session.observer cursor _
    rw [hm]
    simp only [bind_ok]
    cases label with
    | none => exact ⟨middle, rfl⟩
    | some label =>
      obtain ⟨final, hf⟩ := ht.annotate middle label
      exact ⟨final, by simp [hf]⟩

/-- Any terminating child's outcome, cursor, output and backend transition are
preserved by the extracted scope, under the child's observer-independence contract. -/
theorem scoped_preserves {B O M P T : Type} (hooks : Observe O M) (ht : HooksTotal hooks)
    (child : Eval P (Session B O) T) (parser : Scoped P) (session : Session B O)
    (input : Slice U8) (cursor : Cursor) (context : ParseContext)
    (result : ParseOutcome T) (after : B)
    (hc : ∀ observer, ∃ final,
      child.eval parser.parser { session with observer } input cursor context =
        .ok (result, { backend := after, observer := final })) :
    ∃ final, Scoped.Insts.RusthammerParser_traitsEvalInputSessionClause1_Clause0_Output.eval
      hooks child parser session input cursor context =
        .ok (result, { backend := after, observer := final }) := by
  obtain ⟨⟨mark, initial⟩, hi⟩ := ht.begin session.observer
  obtain ⟨middle, hm⟩ := hc initial
  obtain ⟨decorated, hd⟩ := decorate_preserves hooks ht ⟨after, middle⟩ cursor parser.label result
  obtain ⟨final, hf⟩ := close_preserves hooks ht ⟨after, decorated⟩ mark result
  exact ⟨final, by
    simp [Scoped.Insts.RusthammerParser_traitsEvalInputSessionClause1_Clause0_Output.eval,
      hi, hm, hd, hf]⟩

def literalResult (expected : U8) (result : ParseOutcome U8) : ParseOutcome U8 :=
  match result with
  | .Success next byte => if byte = expected then .Success next byte else .Error .Mismatch
  | .Error error => .Error error
  | .NeedMore => .NeedMore

theorem observe_byte_preserves {B O M : Type} (hooks : Observe O M) (ht : HooksTotal hooks)
    (session : Session B O) (cursor : Cursor) (length : Usize) (expected : U8)
    (result : ParseOutcome U8) :
    ∃ observer, observe_byte hooks session cursor length expected result =
      .ok (literalResult expected result, { session with observer }) := by
  cases result with
  | Success next byte =>
    by_cases h : byte = expected
    · exact ⟨session.observer, by simp [observe_byte, literalResult, h]⟩
    · obtain ⟨observer, ho⟩ := ht.record session.observer
        ⟨cursor, true, .Rejected .Mismatch, .Byte expected, none, none, false⟩
      exact ⟨observer, by simp [observe_byte, literalResult, h, Failure.new, ho]⟩
  | Error error =>
    let location : Cursor := match error with
      | .UnexpectedEnd => ⟨length, 0#u8⟩
      | _ => cursor
    obtain ⟨observer, ho⟩ := ht.record session.observer
      ⟨location, true, .Rejected error, .Byte expected, none, none, false⟩
    cases error
    all_goals
      refine ⟨observer, ?_⟩
      simp only [location] at ho
      simp [observe_byte, literalResult, Failure.new, ho]
  | NeedMore =>
    obtain ⟨observer, ho⟩ := ht.record session.observer
      ⟨⟨length, 0#u8⟩, true, .Incomplete, .Byte expected, none, none, false⟩
    exact ⟨observer, by simp [observe_byte, literalResult, Failure.new, ho]⟩

local notation "byteEval" => Byte.Insts.RusthammerParser_traitsEvalInputBackendU8.eval

/-- The actual extracted production byte reader, with its empty state projected away. -/
def readByte (input : Slice U8) (cursor : Cursor) (context : ParseContext) :
    Result (ParseOutcome U8) := do
  let (result, _) ← byteEval () () input cursor context
  .ok result

theorem byte_backend_eq {B : Type} (backend : B) (input : Slice U8) (cursor : Cursor)
    (context : ParseContext) :
    byteEval () backend input cursor context =
      (do let result ← readByte input cursor context; .ok (result, backend)) := by
  simp +zeta only [readByte, Byte.Insts.RusthammerParser_traitsEvalInputBackendU8.eval,
    Bits.Insts.RusthammerParser_traitsEvalInputBackendU64.eval, Std.bind_assoc, bind_ok]
  congr 1
  funext value
  congr 1
  funext outcome
  cases outcome <;> simp [Std.bind_assoc]

/-- For any total observer, erasing the diagnostic state gives the same labelled
literal parser. This equality also preserves the underlying reader's modeled
execution failures/divergence; it does not assume the reader returned success. -/
theorem sample_erases {O M : Type} (hooks : Observe O M) (ht : HooksTotal hooks)
    (observer : O) (label : Label) (input : Slice U8) (cursor : Cursor) (context : ParseContext) :
    (do let (result, _) ← sample hooks observer label input cursor context; .ok result) =
      (do let result ← readByte input cursor context; .ok (literalResult 65#u8 result)) := by
  obtain ⟨⟨mark, initial⟩, hi⟩ := ht.begin observer
  simp only [sample, labelled, bind_ok, uncurry,
    Scoped.Insts.RusthammerParser_traitsEvalInputSessionClause1_Clause0_Output.eval, hi,
    ByteEq.Insts.RusthammerParser_traitsEvalInputSessionU8.eval, byte_backend_eq,
    Std.bind_assoc, bind_ok]
  simp only [bind_tc_eq, Std.bind_assoc]
  apply congrArg (Std.bind (readByte input cursor context))
  funext result
  obtain ⟨middle, hm⟩ := observe_byte_preserves hooks ht ⟨(), initial⟩ cursor
    (Slice.len input) 65#u8 result
  obtain ⟨decorated, hd⟩ := decorate_preserves hooks ht ⟨(), middle⟩ cursor (some label)
    (literalResult 65#u8 result)
  obtain ⟨final, hf⟩ := close_preserves hooks ht ⟨(), decorated⟩ mark
    (literalResult 65#u8 result)
  simp [hm, hd, hf]

/-- Enabling concrete diagnostic collection preserves every parse outcome,
including its value and returned cursor, for the labelled byte grammar. -/
theorem run_erases (label : Label) (input : Slice U8) (cursor : Cursor) (context : ParseContext) :
    (do let (result, _) ← run label input cursor context; .ok result) =
      quiet label input cursor context := by
  simp only [run, Report.empty, bind_ok, quiet, Std.bind_assoc, uncurry]
  exact (sample_erases collecting collecting_total _ label input cursor context).trans
    (sample_erases silent silent_total () label input cursor context).symm

#print axioms collecting_total
#print axioms close_preserves
#print axioms decorate_preserves
#print axioms scoped_preserves
#print axioms observe_byte_preserves
#print axioms run_erases

end DiagnosticProbe.Preservation
