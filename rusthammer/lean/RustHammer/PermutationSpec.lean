import RustHammer.ControlSpec

open Aeneas Aeneas.Std

namespace RustHammer.Permutation
open Code

/-- A mathematical entry interpreter includes its output storage and backend
transition. It need not consume input, and may retain effects on rejection. -/
abbrev AttemptFn (S B : Type) := S → Nat → B → Cursor → (permutation.Attempt × S) × B

/-- Ordered depth-first permutation semantics. Natural-number counters are
unbounded; termination depends on the number of remaining entries and candidates,
not on input consumption. An incomplete or fatal child stops the entire search.
After a rejected suffix, retry at the original cursor with the resulting backend. -/
def searchModel {S B : Type} (count : Nat) (used : S → Nat → Bool)
    (clear : S → Nat → S) (attempt : AttemptFn S B)
    (remaining index : Nat) (allAbsent : Bool) (state : S) (backend : B)
    (cursor : Cursor) : (ParseOutcome Unit × S) × B :=
  if remaining = 0 then ((.Success cursor (), state), backend)
  else if index ≥ count then
    ((if allAbsent then .Success cursor () else .Error .Mismatch, state), backend)
  else if used state index then
    searchModel count used clear attempt remaining (index + 1) allAbsent state backend cursor
  else
    let ((result, nextState), nextBackend) := attempt state index backend cursor
    match result with
    | .NeedMore => ((.NeedMore, nextState), nextBackend)
    | .Error error =>
        if Spec.recoverable error then
          searchModel count used clear attempt remaining (index + 1) false nextState nextBackend cursor
        else ((.Error error, nextState), nextBackend)
    | .Absent =>
        searchModel count used clear attempt remaining (index + 1) allAbsent nextState nextBackend cursor
    | .Matched next =>
        let ((suffix, finalState), finalBackend) :=
          searchModel count used clear attempt (remaining - 1) 0 true nextState nextBackend next
        match suffix with
        | .Error error =>
            if Spec.recoverable error then
              searchModel count used clear attempt remaining (index + 1) false
                (clear finalState index) finalBackend cursor
            else ((.Error error, finalState), finalBackend)
        | _ => ((suffix, finalState), finalBackend)
termination_by (remaining, count - index)
decreasing_by all_goals simp_all; omega

/-- The final projection preserves declaration order through the layout's typed
finish function. Only successful searches inspect the stored values. -/
def finishModel {S B O : Type} (finish : S → core.result.Result O ParseError)
    (result : (ParseOutcome Unit × S) × B) : ParseOutcome O × B :=
  match result with
  | ((.Success next (), state), backend) =>
      (match finish state with
       | .Ok value => .Success next value
       | .Err error => .Error error, backend)
  | ((.Error error, _), backend) => (.Error error, backend)
  | ((.NeedMore, _), backend) => (.NeedMore, backend)

end RustHammer.Permutation
