import RustHammer.PartialSpec

open RustHammer.Code.grammar.transform
  RustHammer.Code.input_types

open Aeneas Aeneas.Std

namespace RustHammer.Spec
open Code

/-- Inclusive bounds use the output type's ordering, without converting types. -/
abbrev inRange {T : Type} (le : T → T → Prop) (lower upper value : T) : Prop :=
  le lower value ∧ le value upper

def validIntRange {P T : Type} (le : T → T → Prop) (parser : IntRange P T) : Prop :=
  le parser.lower parser.upper

def intRangeNewOutcome {P T : Type} (le : T → T → Prop) [DecidableRel le]
    (parser : P) (lower upper : T) (result : core.result.Result (IntRange P T) ConfigError) : Prop :=
  if le lower upper then result = .Ok { parser, lower, upper }
  else result = .Err .InvalidBounds

/-- Both status-aware and complete range contracts reuse the existing Verify
relations with `inRange` as their predicate. This preserves the child's input
validation, decoded value, consumed cursor, errors, and incompleteness rules. -/
abbrev intRange {T : Type} (child : Cursor → ParseResult T → Prop)
    (le : T → T → Prop) [DecidableRel le] (lower upper : T) :=
  verify child (inRange le lower upper)

end RustHammer.Spec
