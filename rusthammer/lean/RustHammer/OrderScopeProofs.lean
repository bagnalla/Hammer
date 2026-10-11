import RustHammer.OrderProofs

open RustHammer.Code.grammar.order RustHammer.Code.input_types
open Aeneas Aeneas.Std Result WP

namespace RustHammer.Ordering
open Code

/-- A byte-order scope is transparent apart from the order passed to its child. -/
theorem with_byte_order_spec {P α : Type} (pi : parser_traits.Parser P α)
    (parser : WithByteOrder P) (input : Slice U8) (cursor : Cursor) (ambient : ByteOrder)
    (contract : Spec.ParseResult α → Prop)
    (hp : pi.parse_with parser.parser input cursor parser.byte_order
      ⦃ result => contract result ⦄) :
    WithByteOrder.Insts.RusthammerParser_traitsParser.parse_with pi parser input cursor ambient
      ⦃ result => contract result ⦄ := by
  exact hp

end RustHammer.Ordering
