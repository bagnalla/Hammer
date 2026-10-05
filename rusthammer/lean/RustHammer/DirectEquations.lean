import RustHammer.Direct

/-! Equations for the direct views, proved against the extracted evaluators.
They expose one layer of control flow while projecting away `Direct`'s unit
state, so existing compositional specifications apply to the refactored Rust.
There is no independent executable interpreter in this file. -/

open Aeneas Aeneas.Std Result
namespace RustHammer.Code
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option maxRecDepth 2048

macro "direct_equation" : tactic => `(tactic| (
  try simp only [direct_lift]
  iterate 10 (
    all_goals try simp_all [direct_lift]
    all_goals try rfl
    all_goals try (casesm* _ × _)
    all_goals try split
    all_goals try (congr 1; funext parsed; cases parsed))))

theorem Bits.Insts.RusthammerParserInputU64.parse_with_eq (self : Bits) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Bits.Insts.RusthammerParserInputU64.parse_with self input cursor context = (do
  let r ← read_ordered_bits input cursor self context.order
  InputStatus.classify context.status r) := by
  conv_lhs =>
    unfold Bits.Insts.RusthammerParserInputU64.parse_with DirectParser.parse_with
    dsimp only [Bits.Insts.RusthammerParserInputU64, Bits.Insts.RusthammerEvalInputBackendU64]
    unfold Bits.Insts.RusthammerEvalInputBackendU64.eval
  try simp only [dependent_examples.count_parser, record_example.record_header, bind_ok]
  direct_equation

theorem dependent_examples.CountPrefix.Insts.RusthammerParserInputUsize.parse_with_eq (self : dependent_examples.CountPrefix) (input : Slice Std.U8)
  (cursor : Cursor) (context : ParseContext) :
  dependent_examples.CountPrefix.Insts.RusthammerParserInputUsize.parse_with self input cursor context = (do
  let b ← dependent_examples.fixed_bits 8#u8
  TryMap.Insts.RusthammerParser.parse_with Bits.Insts.RusthammerParserInputU64
    dependent_examples.ParserInputCountPrefixUsize.parse_with.closure.Insts.CoreOpsFunctionFnTupleU64ResultUsizeTuple
    { parser := b, map := () } input cursor context) := by
  conv_lhs =>
    unfold dependent_examples.CountPrefix.Insts.RusthammerParserInputUsize.parse_with DirectParser.parse_with
    dsimp only [dependent_examples.CountPrefix.Insts.RusthammerParserInputUsize, dependent_examples.CountPrefix.Insts.RusthammerEvalInputBackendUsize]
    unfold dependent_examples.CountPrefix.Insts.RusthammerEvalInputBackendUsize.eval
  try simp only [dependent_examples.count_parser, record_example.record_header, bind_ok]
  direct_equation

theorem TakeAligned.Insts.RusthammerParserInputSharedInputSliceU8.parse_with_eq (self : TakeAligned) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  TakeAligned.Insts.RusthammerParserInputSharedInputSliceU8.parse_with self input cursor context = (do
  let r ← take_aligned input cursor self.count
  InputStatus.classify context.status r) := by
  conv_lhs =>
    unfold TakeAligned.Insts.RusthammerParserInputSharedInputSliceU8.parse_with DirectParser.parse_with
    dsimp only [TakeAligned.Insts.RusthammerParserInputSharedInputSliceU8, TakeAligned.Insts.RusthammerEvalInputBackendSharedSliceU8]
    unfold TakeAligned.Insts.RusthammerEvalInputBackendSharedSliceU8.eval
  try simp only [dependent_examples.count_parser, record_example.record_header, bind_ok]
  direct_equation

theorem Repeat.Insts.RusthammerParserInputVec.parse_with_eq {P : Type} {Clause0_Output : Type} (ParserInst : DirectParser P Clause0_Output)
  (self : Repeat P) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Repeat.Insts.RusthammerParserInputVec.parse_with ParserInst self input cursor context = (do
  DirectRun.repeat_run ParserInst (Collect.Insts.RusthammerRepeatAccumulatorAVec
    Clause0_Output) self.parser self.bounds () input cursor context) := by
  conv_lhs =>
    unfold Repeat.Insts.RusthammerParserInputVec.parse_with DirectParser.parse_with
    dsimp only [Repeat.Insts.RusthammerParserInputVec, Repeat.Insts.RusthammerEvalInputBackendVec]
    unfold Repeat.Insts.RusthammerEvalInputBackendVec.eval
  try simp only [dependent_examples.count_parser, record_example.record_header, bind_ok]
  direct_equation

theorem Map.Insts.RusthammerParser.parse_with_eq {P : Type} {F : Type} {O : Type} {Clause0_Output : Type} (ParserInst : DirectParser
  P Clause0_Output) (coreopsfunctionFnFTupleClause0_OutputOInst :
  core.ops.function.Fn F Clause0_Output O) (self : Map P F)
  (input : Slice Std.U8) (cursor : Cursor) (context : ParseContext) :
  Map.Insts.RusthammerParser.parse_with ParserInst coreopsfunctionFnFTupleClause0_OutputOInst self input cursor context = (do
  let po ← ParserInst.parse_with self.parser input cursor context
  match po with
  | ParseOutcome.Success next value =>
    let t ← coreopsfunctionFnFTupleClause0_OutputOInst.call self.map value
    ok (ParseOutcome.Success next t)
  | ParseOutcome.Error error => ok (ParseOutcome.Error error)
  | ParseOutcome.NeedMore => ok ParseOutcome.NeedMore) := by
  conv_lhs =>
    unfold Map.Insts.RusthammerParser.parse_with DirectParser.parse_with
    dsimp only [Map.Insts.RusthammerParser, Map.Insts.RusthammerEval]
    unfold Map.Insts.RusthammerEval.eval
  try simp only [dependent_examples.count_parser, record_example.record_header, bind_ok]
  direct_equation

theorem Seq.Insts.RusthammerParserInputPair.parse_with_eq {P : Type} {Q : Type} {Clause0_Output : Type} {Clause1_Output : Type}
  (ParserInst : DirectParser P Clause0_Output) (ParserInst1 : DirectParser Q
  Clause1_Output) (self : Seq P Q) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Seq.Insts.RusthammerParserInputPair.parse_with ParserInst ParserInst1 self input cursor context = (do
  let po ← ParserInst.parse_with self.first input cursor context
  match po with
  | ParseOutcome.Success next first =>
    let po1 ← ParserInst1.parse_with self.second input next context
    match po1 with
    | ParseOutcome.Success «end» second =>
      ok (ParseOutcome.Success «end» (first, second))
    | ParseOutcome.Error error => ok (ParseOutcome.Error error)
    | ParseOutcome.NeedMore => ok ParseOutcome.NeedMore
  | ParseOutcome.Error error => ok (ParseOutcome.Error error)
  | ParseOutcome.NeedMore => ok ParseOutcome.NeedMore) := by
  conv_lhs =>
    unfold Seq.Insts.RusthammerParserInputPair.parse_with DirectParser.parse_with
    dsimp only [Seq.Insts.RusthammerParserInputPair, Seq.Insts.RusthammerEvalInputBackendPair]
    unfold Seq.Insts.RusthammerEvalInputBackendPair.eval
  try simp only [dependent_examples.count_parser, record_example.record_header, bind_ok]
  direct_equation

theorem Bit.Insts.RusthammerParserInputBool.parse_with_eq (self : Bit) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Bit.Insts.RusthammerParserInputBool.parse_with self input cursor context = (do
  let r ← read_bit_ordered input cursor context.order.bit
  InputStatus.classify context.status r) := by
  conv_lhs =>
    unfold Bit.Insts.RusthammerParserInputBool.parse_with DirectParser.parse_with
    dsimp only [Bit.Insts.RusthammerParserInputBool, Bit.Insts.RusthammerEvalInputBackendBool]
    unfold Bit.Insts.RusthammerEvalInputBackendBool.eval
  try simp only [dependent_examples.count_parser, record_example.record_header, bind_ok]
  direct_equation

theorem Choice.Insts.RusthammerParser.parse_with_eq {P : Type} {Q : Type} {Clause0_Output : Type} (ParserInst : DirectParser P
  Clause0_Output) (ParserInst1 : DirectParser Q Clause0_Output) (self : Choice P Q)
  (input : Slice Std.U8) (cursor : Cursor) (context : ParseContext) :
  Choice.Insts.RusthammerParser.parse_with ParserInst ParserInst1 self input cursor context = (do
  let po ← ParserInst.parse_with self.first input cursor context
  match po with
  | ParseOutcome.Success _ _ => ok po
  | ParseOutcome.Error error =>
    let b ← ParseError.is_recoverable error
    if b
    then ParserInst1.parse_with self.second input cursor context
    else ok po
  | ParseOutcome.NeedMore => ok ParseOutcome.NeedMore) := by
  conv_lhs =>
    unfold Choice.Insts.RusthammerParser.parse_with DirectParser.parse_with
    dsimp only [Choice.Insts.RusthammerParser, Choice.Insts.RusthammerEval]
    unfold Choice.Insts.RusthammerEval.eval
  try simp only [dependent_examples.count_parser, record_example.record_header, bind_ok]
  direct_equation

theorem End.Insts.RusthammerParserInputTuple.parse_with_eq (self : End) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  End.Insts.RusthammerParserInputTuple.parse_with self input cursor context = (do
  if cursor.bit >= 8#u8
  then ok (ParseOutcome.Error ParseError.InvalidCursor)
  else
    let i := Slice.len input
    if cursor.byte > i
    then ok (ParseOutcome.Error ParseError.InvalidCursor)
    else
      let i1 := Slice.len input
      if cursor.byte = i1
      then
        if cursor.bit != 0#u8
        then ok (ParseOutcome.Error ParseError.InvalidCursor)
        else
          let i2 := Slice.len input
          if cursor.byte = i2
          then
            match context.status with
            | InputStatus.Partial => ok ParseOutcome.NeedMore
            | InputStatus.Final => ok (ParseOutcome.Success cursor ())
          else ok (ParseOutcome.Error ParseError.TrailingInput)
      else
        let i2 := Slice.len input
        if cursor.byte = i2
        then
          match context.status with
          | InputStatus.Partial => ok ParseOutcome.NeedMore
          | InputStatus.Final => ok (ParseOutcome.Success cursor ())
        else ok (ParseOutcome.Error ParseError.TrailingInput)) := by
  conv_lhs =>
    unfold End.Insts.RusthammerParserInputTuple.parse_with DirectParser.parse_with
    dsimp only [End.Insts.RusthammerParserInputTuple, End.Insts.RusthammerEvalInputBackendTuple]
    unfold End.Insts.RusthammerEvalInputBackendTuple.eval
  try simp only [dependent_examples.count_parser, record_example.record_header, bind_ok]
  direct_equation

theorem Literal.Insts.RusthammerParserInputU64.parse_with_eq (self : Literal) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Literal.Insts.RusthammerParserInputU64.parse_with self input cursor context = (do
  let r ← read_literal input cursor self context.order
  InputStatus.classify context.status r) := by
  conv_lhs =>
    unfold Literal.Insts.RusthammerParserInputU64.parse_with DirectParser.parse_with
    dsimp only [Literal.Insts.RusthammerParserInputU64, Literal.Insts.RusthammerEvalInputBackendU64]
    unfold Literal.Insts.RusthammerEvalInputBackendU64.eval
  try simp only [dependent_examples.count_parser, record_example.record_header, bind_ok]
  direct_equation

theorem marker_example.Marker.Insts.RusthammerParserInputU64.parse_with_eq (self : marker_example.Marker) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  marker_example.Marker.Insts.RusthammerParserInputU64.parse_with self input cursor context = (do
  let po ←
    Seq.Insts.RusthammerParserInputPair.parse_with
      (Choice.Insts.RusthammerParser Literal.Insts.RusthammerParserInputU64
      Literal.Insts.RusthammerParserInputU64)
      End.Insts.RusthammerParserInputTuple self.parser input cursor context
  match po with
  | ParseOutcome.Success next p =>
    let (value, _) := p
    ok (ParseOutcome.Success next value)
  | ParseOutcome.Error error => ok (ParseOutcome.Error error)
  | ParseOutcome.NeedMore => ok ParseOutcome.NeedMore) := by
  conv_lhs =>
    unfold marker_example.Marker.Insts.RusthammerParserInputU64.parse_with DirectParser.parse_with
    dsimp only [marker_example.Marker.Insts.RusthammerParserInputU64, marker_example.Marker.Insts.RusthammerEvalInputBackendU64]
    unfold marker_example.Marker.Insts.RusthammerEvalInputBackendU64.eval
  try simp only [dependent_examples.count_parser, record_example.record_header, bind_ok]
  direct_equation

theorem record_example.RecordParser.Insts.RusthammerParserInputRecord.parse_with_eq (self : record_example.RecordParser) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  record_example.RecordParser.Insts.RusthammerParserInputRecord.parse_with self input cursor context = (do
  let po ←
    TakeAligned.Insts.RusthammerParserInputSharedInputSliceU8.parse_with
      { count := 0#usize } input cursor context
  match po with
  | ParseOutcome.Success _ _ =>
    let po1 ←
      Verify.Insts.RusthammerParser.parse_with
        (Seq.Insts.RusthammerParserInputPair
        Bits.Insts.RusthammerParserInputU64
        (Seq.Insts.RusthammerParserInputPair
        Bits.Insts.RusthammerParserInputU64
        Bits.Insts.RusthammerParserInputU64))
        record_example.ParserInputRecordParserRecord.parse_with.closure.Insts.CoreOpsFunctionFnTupleShared0PairU64PairU64U64Bool
        {
          parser :=
            {
              first := self.version,
              second := { first := self.flags, second := self.length }
            },
          predicate := ()
        } input cursor context
    match po1 with
    | ParseOutcome.Success next p =>
      let (version, (flags, length)) := p
      let i ← lift (UScalar.cast .Usize length)
      DirectRun.record_example.parse_record_body input next version flags i context
    | ParseOutcome.Error error => ok (ParseOutcome.Error error)
    | ParseOutcome.NeedMore => ok ParseOutcome.NeedMore
  | ParseOutcome.Error error => ok (ParseOutcome.Error error)
  | ParseOutcome.NeedMore => ok ParseOutcome.NeedMore) := by
  conv_lhs =>
    unfold record_example.RecordParser.Insts.RusthammerParserInputRecord.parse_with DirectParser.parse_with
    dsimp only [record_example.RecordParser.Insts.RusthammerParserInputRecord, record_example.RecordParser.Insts.RusthammerEvalInputBackendRecord]
    unfold record_example.RecordParser.Insts.RusthammerEvalInputBackendRecord.eval
  try simp only [dependent_examples.count_parser, record_example.record_header, bind_ok]
  direct_equation

theorem SkipBits.Insts.RusthammerParserInputTuple.parse_with_eq (self : SkipBits) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  SkipBits.Insts.RusthammerParserInputTuple.parse_with self input cursor context = (do
  let i := Slice.len input
  let r ← advance_cursor i cursor self.bits
  let result ←
    match r with
    | core.result.Result.Ok next => ok (core.result.Result.Ok (next, ()))
    | core.result.Result.Err error => ok (core.result.Result.Err error)
  InputStatus.classify context.status result) := by
  conv_lhs =>
    unfold SkipBits.Insts.RusthammerParserInputTuple.parse_with DirectParser.parse_with
    dsimp only [SkipBits.Insts.RusthammerParserInputTuple, SkipBits.Insts.RusthammerEvalInputBackendTuple]
    unfold SkipBits.Insts.RusthammerEvalInputBackendTuple.eval
  try simp only [dependent_examples.count_parser, record_example.record_header, bind_ok]
  direct_equation

theorem Tell.Insts.RusthammerParserInputCursor.parse_with_eq (self : Tell) (input : Slice Std.U8) (cursor : Cursor)
  (_context : ParseContext) :
  Tell.Insts.RusthammerParserInputCursor.parse_with self input cursor _context = (do
  let i := Slice.len input
  let r ← advance_cursor i cursor 0#usize
  match r with
  | core.result.Result.Ok next => ok (ParseOutcome.Success next next)
  | core.result.Result.Err error => ok (ParseOutcome.Error error)) := by
  conv_lhs =>
    unfold Tell.Insts.RusthammerParserInputCursor.parse_with DirectParser.parse_with
    dsimp only [Tell.Insts.RusthammerParserInputCursor, Tell.Insts.RusthammerEvalInputBackendCursor]
    unfold Tell.Insts.RusthammerEvalInputBackendCursor.eval
  try simp only [dependent_examples.count_parser, record_example.record_header, bind_ok]
  direct_equation

theorem Shared0P.Insts.RusthammerParser.parse_with_eq {P : Type} {Clause0_Output : Type} (ParserInst : DirectParser P Clause0_Output)
  (self : P) (input : Slice Std.U8) (cursor : Cursor) (context : ParseContext) :
  Shared0P.Insts.RusthammerParser.parse_with ParserInst self input cursor context = (do
  ParserInst.parse_with self input cursor context) := by
  conv_lhs =>
    unfold Shared0P.Insts.RusthammerParser.parse_with DirectParser.parse_with
    dsimp only [Shared0P.Insts.RusthammerParser, Shared0P.Insts.RusthammerEval]
    unfold Shared0P.Insts.RusthammerEval.eval
  try simp only [dependent_examples.count_parser, record_example.record_header, bind_ok]
  direct_equation

theorem WithOrder.Insts.RusthammerParser.parse_with_eq {P : Type} {Clause0_Output : Type} (ParserInst : DirectParser P Clause0_Output)
  (self : WithOrder P) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  WithOrder.Insts.RusthammerParser.parse_with ParserInst self input cursor context = (do
  let changed ←
    core.cmp.PartialEq.ne.trait_default BitOrder.Insts.CoreCmpPartialEqBitOrder
      self.order.bit context.order.bit
  if changed
  then
    let i := Slice.len input
    let o ← scope_boundary_error i cursor
    match o with
    | none =>
      let result ←
        ParserInst.parse_with self.parser input cursor
          { context with order := self.order }
      let i1 := Slice.len input
      finish_order_scope i1 changed result
    | some error => ok (ParseOutcome.Error error)
  else
    let result ←
      ParserInst.parse_with self.parser input cursor
        { context with order := self.order }
    let i := Slice.len input
    finish_order_scope i changed result) := by
  conv_lhs =>
    unfold WithOrder.Insts.RusthammerParser.parse_with DirectParser.parse_with
    dsimp only [WithOrder.Insts.RusthammerParser, WithOrder.Insts.RusthammerEval]
    unfold WithOrder.Insts.RusthammerEval.eval
  try simp only [dependent_examples.count_parser, record_example.record_header, bind_ok]
  direct_equation

theorem SignedBits.Insts.RusthammerParserInputI64.parse_with_eq (self : SignedBits) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  SignedBits.Insts.RusthammerParserInputI64.parse_with self input cursor context = (do
  let po ←
    Bits.Insts.RusthammerParserInputU64.parse_with self.bits input cursor
      context
  match po with
  | ParseOutcome.Success next value =>
    let i ← sign_extend value self.bits.width
    ok (ParseOutcome.Success next i)
  | ParseOutcome.Error error => ok (ParseOutcome.Error error)
  | ParseOutcome.NeedMore => ok ParseOutcome.NeedMore) := by
  conv_lhs =>
    unfold SignedBits.Insts.RusthammerParserInputI64.parse_with DirectParser.parse_with
    dsimp only [SignedBits.Insts.RusthammerParserInputI64, SignedBits.Insts.RusthammerEvalInputBackendI64]
    unfold SignedBits.Insts.RusthammerEvalInputBackendI64.eval
  try simp only [dependent_examples.count_parser, record_example.record_header, bind_ok]
  direct_equation

theorem Byte.Insts.RusthammerParserInputU8.parse_with_eq (self : Byte) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Byte.Insts.RusthammerParserInputU8.parse_with self input cursor context = (do
  let po ←
    Bits.Insts.RusthammerParserInputU64.parse_with { width := 8#u8 } input
      cursor context
  match po with
  | ParseOutcome.Success next value =>
    let i ← lift (UScalar.cast .U8 value)
    ok (ParseOutcome.Success next i)
  | ParseOutcome.Error error => ok (ParseOutcome.Error error)
  | ParseOutcome.NeedMore => ok ParseOutcome.NeedMore) := by
  conv_lhs =>
    unfold Byte.Insts.RusthammerParserInputU8.parse_with DirectParser.parse_with
    dsimp only [Byte.Insts.RusthammerParserInputU8, Byte.Insts.RusthammerEvalInputBackendU8]
    unfold Byte.Insts.RusthammerEvalInputBackendU8.eval
  try simp only [dependent_examples.count_parser, record_example.record_header, bind_ok]
  direct_equation

theorem BeU16.Insts.RusthammerParserInputU16.parse_with_eq (self : BeU16) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  BeU16.Insts.RusthammerParserInputU16.parse_with self input cursor context = (do
  let po ←
    Bits.Insts.RusthammerParserInputU64.parse_with { width := 16#u8 } input
      cursor
      { context with order := { context.order with byte := ByteOrder.Big } }
  match po with
  | ParseOutcome.Success next value =>
    let i ← lift (UScalar.cast .U16 value)
    ok (ParseOutcome.Success next i)
  | ParseOutcome.Error error => ok (ParseOutcome.Error error)
  | ParseOutcome.NeedMore => ok ParseOutcome.NeedMore) := by
  conv_lhs =>
    unfold BeU16.Insts.RusthammerParserInputU16.parse_with DirectParser.parse_with
    dsimp only [BeU16.Insts.RusthammerParserInputU16, BeU16.Insts.RusthammerEvalInputBackendU16]
    unfold BeU16.Insts.RusthammerEvalInputBackendU16.eval
  try simp only [dependent_examples.count_parser, record_example.record_header, bind_ok]
  direct_equation

theorem BeU32.Insts.RusthammerParserInputU32.parse_with_eq (self : BeU32) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  BeU32.Insts.RusthammerParserInputU32.parse_with self input cursor context = (do
  let po ←
    Bits.Insts.RusthammerParserInputU64.parse_with { width := 32#u8 } input
      cursor
      { context with order := { context.order with byte := ByteOrder.Big } }
  match po with
  | ParseOutcome.Success next value =>
    let i ← lift (UScalar.cast .U32 value)
    ok (ParseOutcome.Success next i)
  | ParseOutcome.Error error => ok (ParseOutcome.Error error)
  | ParseOutcome.NeedMore => ok ParseOutcome.NeedMore) := by
  conv_lhs =>
    unfold BeU32.Insts.RusthammerParserInputU32.parse_with DirectParser.parse_with
    dsimp only [BeU32.Insts.RusthammerParserInputU32, BeU32.Insts.RusthammerEvalInputBackendU32]
    unfold BeU32.Insts.RusthammerEvalInputBackendU32.eval
  try simp only [dependent_examples.count_parser, record_example.record_header, bind_ok]
  direct_equation

theorem BeU64.Insts.RusthammerParserInputU64.parse_with_eq (self : BeU64) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  BeU64.Insts.RusthammerParserInputU64.parse_with self input cursor context = (do
  let po ←
    Bits.Insts.RusthammerParserInputU64.parse_with { width := 64#u8 } input
      cursor
      { context with order := { context.order with byte := ByteOrder.Big } }
  match po with
  | ParseOutcome.Success _ _ => ok po
  | ParseOutcome.Error _ => ok po
  | ParseOutcome.NeedMore => ok ParseOutcome.NeedMore) := by
  conv_lhs =>
    unfold BeU64.Insts.RusthammerParserInputU64.parse_with DirectParser.parse_with
    dsimp only [BeU64.Insts.RusthammerParserInputU64, BeU64.Insts.RusthammerEvalInputBackendU64]
    unfold BeU64.Insts.RusthammerEvalInputBackendU64.eval
  try simp only [dependent_examples.count_parser, record_example.record_header, bind_ok]
  direct_equation

theorem I8.Insts.RusthammerParserInputI8.parse_with_eq (self : I8) (input : Slice Std.U8) (cursor : Cursor) (context : ParseContext) :
  I8.Insts.RusthammerParserInputI8.parse_with self input cursor context = (do
  let po ←
    SignedBits.Insts.RusthammerParserInputI64.parse_with
      { bits := { width := 8#u8 } } input cursor context
  match po with
  | ParseOutcome.Success next value =>
    let i ← lift (IScalar.cast .I8 value)
    ok (ParseOutcome.Success next i)
  | ParseOutcome.Error error => ok (ParseOutcome.Error error)
  | ParseOutcome.NeedMore => ok ParseOutcome.NeedMore) := by
  conv_lhs =>
    unfold I8.Insts.RusthammerParserInputI8.parse_with DirectParser.parse_with
    dsimp only [I8.Insts.RusthammerParserInputI8, I8.Insts.RusthammerEvalInputBackendI8]
    unfold I8.Insts.RusthammerEvalInputBackendI8.eval
  try simp only [dependent_examples.count_parser, record_example.record_header, bind_ok]
  direct_equation

theorem BeI16.Insts.RusthammerParserInputI16.parse_with_eq (self : BeI16) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  BeI16.Insts.RusthammerParserInputI16.parse_with self input cursor context = (do
  let po ←
    SignedBits.Insts.RusthammerParserInputI64.parse_with
      { bits := { width := 16#u8 } } input cursor
      { context with order := { context.order with byte := ByteOrder.Big } }
  match po with
  | ParseOutcome.Success next value =>
    let i ← lift (IScalar.cast .I16 value)
    ok (ParseOutcome.Success next i)
  | ParseOutcome.Error error => ok (ParseOutcome.Error error)
  | ParseOutcome.NeedMore => ok ParseOutcome.NeedMore) := by
  conv_lhs =>
    unfold BeI16.Insts.RusthammerParserInputI16.parse_with DirectParser.parse_with
    dsimp only [BeI16.Insts.RusthammerParserInputI16, BeI16.Insts.RusthammerEvalInputBackendI16]
    unfold BeI16.Insts.RusthammerEvalInputBackendI16.eval
  try simp only [dependent_examples.count_parser, record_example.record_header, bind_ok]
  direct_equation

theorem BeI32.Insts.RusthammerParserInputI32.parse_with_eq (self : BeI32) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  BeI32.Insts.RusthammerParserInputI32.parse_with self input cursor context = (do
  let po ←
    SignedBits.Insts.RusthammerParserInputI64.parse_with
      { bits := { width := 32#u8 } } input cursor
      { context with order := { context.order with byte := ByteOrder.Big } }
  match po with
  | ParseOutcome.Success next value =>
    let i ← lift (IScalar.cast .I32 value)
    ok (ParseOutcome.Success next i)
  | ParseOutcome.Error error => ok (ParseOutcome.Error error)
  | ParseOutcome.NeedMore => ok ParseOutcome.NeedMore) := by
  conv_lhs =>
    unfold BeI32.Insts.RusthammerParserInputI32.parse_with DirectParser.parse_with
    dsimp only [BeI32.Insts.RusthammerParserInputI32, BeI32.Insts.RusthammerEvalInputBackendI32]
    unfold BeI32.Insts.RusthammerEvalInputBackendI32.eval
  try simp only [dependent_examples.count_parser, record_example.record_header, bind_ok]
  direct_equation

theorem BeI64.Insts.RusthammerParserInputI64.parse_with_eq (self : BeI64) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  BeI64.Insts.RusthammerParserInputI64.parse_with self input cursor context = (do
  let po ←
    SignedBits.Insts.RusthammerParserInputI64.parse_with
      { bits := { width := 64#u8 } } input cursor
      { context with order := { context.order with byte := ByteOrder.Big } }
  match po with
  | ParseOutcome.Success _ _ => ok po
  | ParseOutcome.Error _ => ok po
  | ParseOutcome.NeedMore => ok ParseOutcome.NeedMore) := by
  conv_lhs =>
    unfold BeI64.Insts.RusthammerParserInputI64.parse_with DirectParser.parse_with
    dsimp only [BeI64.Insts.RusthammerParserInputI64, BeI64.Insts.RusthammerEvalInputBackendI64]
    unfold BeI64.Insts.RusthammerEvalInputBackendI64.eval
  try simp only [dependent_examples.count_parser, record_example.record_header, bind_ok]
  direct_equation

theorem ByteIn.Insts.RusthammerParserInputU8.parse_with_eq (self : ByteIn) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  ByteIn.Insts.RusthammerParserInputU8.parse_with self input cursor context = (do
  Verify.Insts.RusthammerParser.parse_with Byte.Insts.RusthammerParserInputU8
    ParserInputByteInU8.parse_with.closure.Insts.CoreOpsFunctionFnTupleShared1U8Bool
    { parser := (), predicate := self } input cursor context) := by
  conv_lhs =>
    unfold ByteIn.Insts.RusthammerParserInputU8.parse_with DirectParser.parse_with
    dsimp only [ByteIn.Insts.RusthammerParserInputU8, ByteIn.Insts.RusthammerEvalInputBackendU8]
    unfold ByteIn.Insts.RusthammerEvalInputBackendU8.eval
  try simp only [dependent_examples.count_parser, record_example.record_header, bind_ok]
  direct_equation

theorem ByteNotIn.Insts.RusthammerParserInputU8.parse_with_eq (self : ByteNotIn) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  ByteNotIn.Insts.RusthammerParserInputU8.parse_with self input cursor context = (do
  Verify.Insts.RusthammerParser.parse_with Byte.Insts.RusthammerParserInputU8
    ParserInputByteNotInU8.parse_with.closure.Insts.CoreOpsFunctionFnTupleShared1U8Bool
    { parser := (), predicate := self } input cursor context) := by
  conv_lhs =>
    unfold ByteNotIn.Insts.RusthammerParserInputU8.parse_with DirectParser.parse_with
    dsimp only [ByteNotIn.Insts.RusthammerParserInputU8, ByteNotIn.Insts.RusthammerEvalInputBackendU8]
    unfold ByteNotIn.Insts.RusthammerEvalInputBackendU8.eval
  try simp only [dependent_examples.count_parser, record_example.record_header, bind_ok]
  direct_equation

theorem BytePattern.Insts.RusthammerParserInputSharedPatternSliceU8.parse_with_eq (self : BytePattern) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  BytePattern.Insts.RusthammerParserInputSharedPatternSliceU8.parse_with self input cursor context = (do
  let po ← DirectRun.match_byte_pattern self.pattern input cursor context
  match po with
  | ParseOutcome.Success next _ => ok (ParseOutcome.Success next self.pattern)
  | ParseOutcome.Error error => ok (ParseOutcome.Error error)
  | ParseOutcome.NeedMore => ok ParseOutcome.NeedMore) := by
  conv_lhs =>
    unfold BytePattern.Insts.RusthammerParserInputSharedPatternSliceU8.parse_with DirectParser.parse_with
    dsimp only [BytePattern.Insts.RusthammerParserInputSharedPatternSliceU8, BytePattern.Insts.RusthammerEvalInputBackendSharedSliceU8]
    unfold BytePattern.Insts.RusthammerEvalInputBackendSharedSliceU8.eval
  try simp only [dependent_examples.count_parser, record_example.record_header, bind_ok]
  direct_equation

theorem Epsilon.Insts.RusthammerParserInputTuple.parse_with_eq (self : Epsilon) (s : Slice Std.U8) (cursor : Cursor) (pc : ParseContext) :
  Epsilon.Insts.RusthammerParserInputTuple.parse_with self s cursor pc = (do
  ok (ParseOutcome.Success cursor ())) := by
  conv_lhs =>
    unfold Epsilon.Insts.RusthammerParserInputTuple.parse_with DirectParser.parse_with
    dsimp only [Epsilon.Insts.RusthammerParserInputTuple, Epsilon.Insts.RusthammerEvalInputBackendTuple]
    unfold Epsilon.Insts.RusthammerEvalInputBackendTuple.eval
  try simp only [dependent_examples.count_parser, record_example.record_header, bind_ok]
  direct_equation

theorem Fail.Insts.RusthammerParser.parse_with_eq {T : Type} (self : Fail T) (s : Slice Std.U8) (c : Cursor)
  (pc : ParseContext) :
  Fail.Insts.RusthammerParser.parse_with self s c pc = (do
  ok (ParseOutcome.Error ParseError.Mismatch)) := by
  conv_lhs =>
    unfold Fail.Insts.RusthammerParser.parse_with DirectParser.parse_with
    dsimp only [Fail.Insts.RusthammerParser, Fail.Insts.RusthammerEval]
    unfold Fail.Insts.RusthammerEval.eval
  try simp only [dependent_examples.count_parser, record_example.record_header, bind_ok]
  direct_equation

theorem Bind.Insts.RusthammerParser.parse_with_eq {P : Type} {F : Type} {Q : Type} {Clause0_Output : Type} {Clause2_Output :
  Type} (ParserInst : DirectParser P Clause0_Output)
  (coreopsfunctionFnFTupleClause0_OutputQInst : core.ops.function.Fn F
  Clause0_Output Q) (ParserInst1 : DirectParser Q Clause2_Output) (self : Bind P F)
  (input : Slice Std.U8) (cursor : Cursor) (context : ParseContext) :
  Bind.Insts.RusthammerParser.parse_with ParserInst coreopsfunctionFnFTupleClause0_OutputQInst ParserInst1 self input cursor context = (do
  let po ← ParserInst.parse_with self.parser input cursor context
  match po with
  | ParseOutcome.Success next value =>
    let t ← coreopsfunctionFnFTupleClause0_OutputQInst.call self.then value
    ParserInst1.parse_with t input next context
  | ParseOutcome.Error error => ok (ParseOutcome.Error error)
  | ParseOutcome.NeedMore => ok ParseOutcome.NeedMore) := by
  conv_lhs =>
    unfold Bind.Insts.RusthammerParser.parse_with DirectParser.parse_with
    dsimp only [Bind.Insts.RusthammerParser, Bind.Insts.RusthammerEval]
    unfold Bind.Insts.RusthammerEval.eval
  try simp only [dependent_examples.count_parser, record_example.record_header, bind_ok]
  direct_equation

theorem Left.Insts.RusthammerParser.parse_with_eq {P : Type} {Q : Type} {Clause0_Output : Type} {Clause1_Output : Type}
  (ParserInst : DirectParser P Clause0_Output) (ParserInst1 : DirectParser Q
  Clause1_Output) (self : Left P Q) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Left.Insts.RusthammerParser.parse_with ParserInst ParserInst1 self input cursor context = (do
  let po ←
    Seq.Insts.RusthammerParserInputPair.parse_with
      (Shared0P.Insts.RusthammerParser ParserInst)
      (Shared0P.Insts.RusthammerParser ParserInst1)
      { first := self.first, second := self.second } input cursor context
  match po with
  | ParseOutcome.Success next values =>
    let (first, _) := values
    ok (ParseOutcome.Success next first)
  | ParseOutcome.Error error => ok (ParseOutcome.Error error)
  | ParseOutcome.NeedMore => ok ParseOutcome.NeedMore) := by
  conv_lhs =>
    unfold Left.Insts.RusthammerParser.parse_with DirectParser.parse_with
    dsimp only [Left.Insts.RusthammerParser, Left.Insts.RusthammerEval]
    unfold Left.Insts.RusthammerEval.eval
  try simp only [dependent_examples.count_parser, record_example.record_header, bind_ok]
  direct_equation

theorem Right.Insts.RusthammerParser.parse_with_eq {P : Type} {Q : Type} {Clause0_Output : Type} {Clause1_Output : Type}
  (ParserInst : DirectParser P Clause0_Output) (ParserInst1 : DirectParser Q
  Clause1_Output) (self : Right P Q) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Right.Insts.RusthammerParser.parse_with ParserInst ParserInst1 self input cursor context = (do
  let po ←
    Seq.Insts.RusthammerParserInputPair.parse_with
      (Shared0P.Insts.RusthammerParser ParserInst)
      (Shared0P.Insts.RusthammerParser ParserInst1)
      { first := self.first, second := self.second } input cursor context
  match po with
  | ParseOutcome.Success next values =>
    let (_, second) := values
    ok (ParseOutcome.Success next second)
  | ParseOutcome.Error error => ok (ParseOutcome.Error error)
  | ParseOutcome.NeedMore => ok ParseOutcome.NeedMore) := by
  conv_lhs =>
    unfold Right.Insts.RusthammerParser.parse_with DirectParser.parse_with
    dsimp only [Right.Insts.RusthammerParser, Right.Insts.RusthammerEval]
    unfold Right.Insts.RusthammerEval.eval
  try simp only [dependent_examples.count_parser, record_example.record_header, bind_ok]
  direct_equation

theorem Middle.Insts.RusthammerParser.parse_with_eq {L : Type} {P : Type} {R : Type} {Clause0_Output : Type} {Clause1_Output :
  Type} {Clause2_Output : Type} (ParserInst : DirectParser L Clause0_Output)
  (ParserInst1 : DirectParser P Clause1_Output) (ParserInst2 : DirectParser R
  Clause2_Output) (self : Middle L P R) (input : Slice Std.U8)
  (cursor : Cursor) (context : ParseContext) :
  Middle.Insts.RusthammerParser.parse_with ParserInst ParserInst1 ParserInst2 self input cursor context = (do
  let po ←
    Seq.Insts.RusthammerParserInputPair.parse_with
      (Shared0P.Insts.RusthammerParser ParserInst)
      (Seq.Insts.RusthammerParserInputPair (Shared0P.Insts.RusthammerParser
      ParserInst1) (Shared0P.Insts.RusthammerParser ParserInst2))
      {
        first := self.left,
        second := { first := self.parser, second := self.right }
      } input cursor context
  match po with
  | ParseOutcome.Success next values =>
    let (_, (middle, _)) := values
    ok (ParseOutcome.Success next middle)
  | ParseOutcome.Error error => ok (ParseOutcome.Error error)
  | ParseOutcome.NeedMore => ok ParseOutcome.NeedMore) := by
  conv_lhs =>
    unfold Middle.Insts.RusthammerParser.parse_with DirectParser.parse_with
    dsimp only [Middle.Insts.RusthammerParser, Middle.Insts.RusthammerEval]
    unfold Middle.Insts.RusthammerEval.eval
  try simp only [dependent_examples.count_parser, record_example.record_header, bind_ok]
  direct_equation

theorem Ignore.Insts.RusthammerParserInputTuple.parse_with_eq {P : Type} {Clause0_Output : Type} (ParserInst : DirectParser P Clause0_Output)
  (self : Ignore P) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Ignore.Insts.RusthammerParserInputTuple.parse_with ParserInst self input cursor context = (do
  let po ← ParserInst.parse_with self.parser input cursor context
  match po with
  | ParseOutcome.Success next _ => ok (ParseOutcome.Success next ())
  | ParseOutcome.Error error => ok (ParseOutcome.Error error)
  | ParseOutcome.NeedMore => ok ParseOutcome.NeedMore) := by
  conv_lhs =>
    unfold Ignore.Insts.RusthammerParserInputTuple.parse_with DirectParser.parse_with
    dsimp only [Ignore.Insts.RusthammerParserInputTuple, Ignore.Insts.RusthammerEvalInputBackendTuple]
    unfold Ignore.Insts.RusthammerEvalInputBackendTuple.eval
  try simp only [dependent_examples.count_parser, record_example.record_header, bind_ok]
  direct_equation

theorem FoldRepeat.Insts.RusthammerParser.parse_with_eq {P : Type} {I : Type} {F : Type} {R : Type} {Clause0_Output : Type}
  (ParserInst : DirectParser P Clause0_Output) (coreopsfunctionFnITupleRInst :
  core.ops.function.Fn I Unit R) (coreopsfunctionFnFPairRInst :
  core.ops.function.Fn F (R × Clause0_Output) R) (self : FoldRepeat P I F)
  (input : Slice Std.U8) (cursor : Cursor) (context : ParseContext) :
  FoldRepeat.Insts.RusthammerParser.parse_with ParserInst coreopsfunctionFnITupleRInst coreopsfunctionFnFPairRInst self input cursor context = (do
  DirectRun.repeat_run ParserInst (FoldRepeat.Insts.RusthammerRepeatAccumulator P
    coreopsfunctionFnITupleRInst coreopsfunctionFnFPairRInst) self.parser
    self.bounds self input cursor context) := by
  conv_lhs =>
    unfold FoldRepeat.Insts.RusthammerParser.parse_with DirectParser.parse_with
    dsimp only [FoldRepeat.Insts.RusthammerParser, FoldRepeat.Insts.RusthammerEval]
    unfold FoldRepeat.Insts.RusthammerEval.eval
  try simp only [dependent_examples.count_parser, record_example.record_header, bind_ok]
  direct_equation

theorem SepBy.Insts.RusthammerParserInputVec.parse_with_eq {P : Type} {S : Type} {Clause0_Output : Type} {Clause1_Output : Type}
  (ParserInst : DirectParser P Clause0_Output) (ParserInst1 : DirectParser S
  Clause1_Output) (self : SepBy P S) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  SepBy.Insts.RusthammerParserInputVec.parse_with ParserInst ParserInst1 self input cursor context = (do
  DirectRun.repeat_run_with ParserInst (Right.Insts.RusthammerParser
    (Shared0P.Insts.RusthammerParser ParserInst1)
    (Shared0P.Insts.RusthammerParser ParserInst))
    (Collect.Insts.RusthammerRepeatAccumulatorAVec Clause0_Output) self.parser
    { first := self.separator, second := self.parser } self.bounds () input
    cursor context) := by
  conv_lhs =>
    unfold SepBy.Insts.RusthammerParserInputVec.parse_with DirectParser.parse_with
    dsimp only [SepBy.Insts.RusthammerParserInputVec, SepBy.Insts.RusthammerEvalInputBackendVec]
    unfold SepBy.Insts.RusthammerEvalInputBackendVec.eval
  try simp only [dependent_examples.count_parser, record_example.record_header, bind_ok]
  direct_equation

theorem FoldSepBy.Insts.RusthammerParser.parse_with_eq {P : Type} {S : Type} {I : Type} {F : Type} {R : Type} {Clause0_Output :
  Type} {Clause1_Output : Type} (ParserInst : DirectParser P Clause0_Output)
  (ParserInst1 : DirectParser S Clause1_Output) (coreopsfunctionFnITupleRInst :
  core.ops.function.Fn I Unit R) (coreopsfunctionFnFPairRInst :
  core.ops.function.Fn F (R × Clause0_Output) R) (self : FoldSepBy P S I F)
  (input : Slice Std.U8) (cursor : Cursor) (context : ParseContext) :
  FoldSepBy.Insts.RusthammerParser.parse_with ParserInst ParserInst1 coreopsfunctionFnITupleRInst coreopsfunctionFnFPairRInst self input cursor context = (do
  DirectRun.repeat_run_with ParserInst (Right.Insts.RusthammerParser
    (Shared0P.Insts.RusthammerParser ParserInst1)
    (Shared0P.Insts.RusthammerParser ParserInst))
    (FoldSepBy.Insts.RusthammerRepeatAccumulator P S
    coreopsfunctionFnITupleRInst coreopsfunctionFnFPairRInst) self.parser
    { first := self.separator, second := self.parser } self.bounds self input
    cursor context) := by
  conv_lhs =>
    unfold FoldSepBy.Insts.RusthammerParser.parse_with DirectParser.parse_with
    dsimp only [FoldSepBy.Insts.RusthammerParser, FoldSepBy.Insts.RusthammerEval]
    unfold FoldSepBy.Insts.RusthammerEval.eval
  try simp only [dependent_examples.count_parser, record_example.record_header, bind_ok]
  direct_equation

theorem TryMap.Insts.RusthammerParser.parse_with_eq {P : Type} {F : Type} {O : Type} {E : Type} {Clause0_Output : Type}
  (ParserInst : DirectParser P Clause0_Output)
  (coreopsfunctionFnFTupleClause0_OutputResultInst : core.ops.function.Fn F
  Clause0_Output (core.result.Result O E)) (self : TryMap P F)
  (input : Slice Std.U8) (cursor : Cursor) (context : ParseContext) :
  TryMap.Insts.RusthammerParser.parse_with ParserInst coreopsfunctionFnFTupleClause0_OutputResultInst self input cursor context = (do
  let po ← ParserInst.parse_with self.parser input cursor context
  match po with
  | ParseOutcome.Success next value =>
    let r ←
      coreopsfunctionFnFTupleClause0_OutputResultInst.call self.map value
    match r with
    | core.result.Result.Ok mapped => ok (ParseOutcome.Success next mapped)
    | core.result.Result.Err _ => ok (ParseOutcome.Error ParseError.Mismatch)
  | ParseOutcome.Error error => ok (ParseOutcome.Error error)
  | ParseOutcome.NeedMore => ok ParseOutcome.NeedMore) := by
  conv_lhs =>
    unfold TryMap.Insts.RusthammerParser.parse_with DirectParser.parse_with
    dsimp only [TryMap.Insts.RusthammerParser, TryMap.Insts.RusthammerEval]
    unfold TryMap.Insts.RusthammerEval.eval
  try simp only [dependent_examples.count_parser, record_example.record_header, bind_ok]
  direct_equation

theorem Verify.Insts.RusthammerParser.parse_with_eq {P : Type} {F : Type} {Clause0_Output : Type} (ParserInst : DirectParser P
  Clause0_Output) (coreopsfunctionFnFTupleSharedInputClause0_OutputBoolInst :
  core.ops.function.Fn F Clause0_Output Bool) (self : Verify P F)
  (input : Slice Std.U8) (cursor : Cursor) (context : ParseContext) :
  Verify.Insts.RusthammerParser.parse_with ParserInst coreopsfunctionFnFTupleSharedInputClause0_OutputBoolInst self input cursor context = (do
  let po ← ParserInst.parse_with self.parser input cursor context
  match po with
  | ParseOutcome.Success _ value =>
    let b ←
      coreopsfunctionFnFTupleSharedInputClause0_OutputBoolInst.call
        self.predicate value
    if b
    then ok po
    else ok (ParseOutcome.Error ParseError.Mismatch)
  | ParseOutcome.Error _ => ok po
  | ParseOutcome.NeedMore => ok ParseOutcome.NeedMore) := by
  conv_lhs =>
    unfold Verify.Insts.RusthammerParser.parse_with DirectParser.parse_with
    dsimp only [Verify.Insts.RusthammerParser, Verify.Insts.RusthammerEval]
    unfold Verify.Insts.RusthammerEval.eval
  try simp only [dependent_examples.count_parser, record_example.record_header, bind_ok]
  direct_equation

theorem IntRange.Insts.RusthammerParser.parse_with_eq {P : Type} {T : Type} (ParserInst : DirectParser P T) (corecmpOrdInst :
  core.cmp.Ord T) (self : IntRange P T) (input : Slice Std.U8)
  (cursor : Cursor) (context : ParseContext) :
  IntRange.Insts.RusthammerParser.parse_with ParserInst corecmpOrdInst self input cursor context = (do
  Verify.Insts.RusthammerParser.parse_with (Shared0P.Insts.RusthammerParser
    ParserInst)
    (ParserInputIntRangeT.parse_with.closure.Insts.CoreOpsFunctionFnTupleShared1TBool
    ParserInst corecmpOrdInst) { parser := self.parser, predicate := self }
    input cursor context) := by
  conv_lhs =>
    unfold IntRange.Insts.RusthammerParser.parse_with DirectParser.parse_with
    dsimp only [IntRange.Insts.RusthammerParser, IntRange.Insts.RusthammerEval]
    unfold IntRange.Insts.RusthammerEval.eval
  try simp only [dependent_examples.count_parser, record_example.record_header, bind_ok]
  direct_equation

theorem ButNot.Insts.RusthammerParser.parse_with_eq {P : Type} {Q : Type} {Clause0_Output : Type} {Clause1_Output : Type}
  (ParserInst : DirectParser P Clause0_Output) (ParserInst1 : DirectParser Q
  Clause1_Output) (self : ButNot P Q) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  ButNot.Insts.RusthammerParser.parse_with ParserInst ParserInst1 self input cursor context = (do
  DirectRun.restrict_match ParserInst ParserInst1 self.first self.second input cursor
    context false) := by
  conv_lhs =>
    unfold ButNot.Insts.RusthammerParser.parse_with DirectParser.parse_with
    dsimp only [ButNot.Insts.RusthammerParser, ButNot.Insts.RusthammerEval]
    unfold ButNot.Insts.RusthammerEval.eval
  try simp only [dependent_examples.count_parser, record_example.record_header, bind_ok]
  direct_equation

theorem Difference.Insts.RusthammerParser.parse_with_eq {P : Type} {Q : Type} {Clause0_Output : Type} {Clause1_Output : Type}
  (ParserInst : DirectParser P Clause0_Output) (ParserInst1 : DirectParser Q
  Clause1_Output) (self : Difference P Q) (input : Slice Std.U8)
  (cursor : Cursor) (context : ParseContext) :
  Difference.Insts.RusthammerParser.parse_with ParserInst ParserInst1 self input cursor context = (do
  DirectRun.restrict_match ParserInst ParserInst1 self.first self.second input cursor
    context true) := by
  conv_lhs =>
    unfold Difference.Insts.RusthammerParser.parse_with DirectParser.parse_with
    dsimp only [Difference.Insts.RusthammerParser, Difference.Insts.RusthammerEval]
    unfold Difference.Insts.RusthammerEval.eval
  try simp only [dependent_examples.count_parser, record_example.record_header, bind_ok]
  direct_equation

theorem Xor.Insts.RusthammerParser.parse_with_eq {P : Type} {Q : Type} {Clause0_Output : Type} (ParserInst : DirectParser P
  Clause0_Output) (ParserInst1 : DirectParser Q Clause0_Output) (self : Xor P Q)
  (input : Slice Std.U8) (cursor : Cursor) (context : ParseContext) :
  Xor.Insts.RusthammerParser.parse_with ParserInst ParserInst1 self input cursor context = (do
  let po ← ParserInst.parse_with self.first input cursor context
  match po with
  | ParseOutcome.Success _ _ =>
    let po1 ← ParserInst1.parse_with self.second input cursor context
    match po1 with
    | ParseOutcome.Success _ _ => ok (ParseOutcome.Error ParseError.Mismatch)
    | ParseOutcome.Error error =>
      let b ← ParseError.is_recoverable error
      if b
      then ok po
      else ok po1
    | ParseOutcome.NeedMore => ok ParseOutcome.NeedMore
  | ParseOutcome.Error error =>
    let b ← ParseError.is_recoverable error
    if b
    then ParserInst1.parse_with self.second input cursor context
    else ok po
  | ParseOutcome.NeedMore => ok ParseOutcome.NeedMore) := by
  conv_lhs =>
    unfold Xor.Insts.RusthammerParser.parse_with DirectParser.parse_with
    dsimp only [Xor.Insts.RusthammerParser, Xor.Insts.RusthammerEval]
    unfold Xor.Insts.RusthammerEval.eval
  try simp only [dependent_examples.count_parser, record_example.record_header, bind_ok]
  direct_equation

theorem Optional.Insts.RusthammerParserInputOption.parse_with_eq {P : Type} {Clause0_Output : Type} (ParserInst : DirectParser P Clause0_Output)
  (self : Optional P) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Optional.Insts.RusthammerParserInputOption.parse_with ParserInst self input cursor context = (do
  let po ← ParserInst.parse_with self.parser input cursor context
  match po with
  | ParseOutcome.Success next value =>
    ok (ParseOutcome.Success next (some value))
  | ParseOutcome.Error error =>
    let b ← ParseError.is_recoverable error
    if b
    then ok (ParseOutcome.Success cursor none)
    else ok (ParseOutcome.Error error)
  | ParseOutcome.NeedMore => ok ParseOutcome.NeedMore) := by
  conv_lhs =>
    unfold Optional.Insts.RusthammerParserInputOption.parse_with DirectParser.parse_with
    dsimp only [Optional.Insts.RusthammerParserInputOption, Optional.Insts.RusthammerEvalInputBackendOption]
    unfold Optional.Insts.RusthammerEvalInputBackendOption.eval
  try simp only [dependent_examples.count_parser, record_example.record_header, bind_ok]
  direct_equation

theorem And.Insts.RusthammerParserInputTuple.parse_with_eq {P : Type} {Clause0_Output : Type} (ParserInst : DirectParser P Clause0_Output)
  (self : And P) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  And.Insts.RusthammerParserInputTuple.parse_with ParserInst self input cursor context = (do
  let po ← ParserInst.parse_with self.parser input cursor context
  match po with
  | ParseOutcome.Success _ _ => ok (ParseOutcome.Success cursor ())
  | ParseOutcome.Error error => ok (ParseOutcome.Error error)
  | ParseOutcome.NeedMore => ok ParseOutcome.NeedMore) := by
  conv_lhs =>
    unfold And.Insts.RusthammerParserInputTuple.parse_with DirectParser.parse_with
    dsimp only [And.Insts.RusthammerParserInputTuple, And.Insts.RusthammerEvalInputBackendTuple]
    unfold And.Insts.RusthammerEvalInputBackendTuple.eval
  try simp only [dependent_examples.count_parser, record_example.record_header, bind_ok]
  direct_equation

theorem Not.Insts.RusthammerParserInputTuple.parse_with_eq {P : Type} {Clause0_Output : Type} (ParserInst : DirectParser P Clause0_Output)
  (self : Not P) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Not.Insts.RusthammerParserInputTuple.parse_with ParserInst self input cursor context = (do
  let po ← ParserInst.parse_with self.parser input cursor context
  match po with
  | ParseOutcome.Success _ _ => ok (ParseOutcome.Error ParseError.Mismatch)
  | ParseOutcome.Error error =>
    let b ← ParseError.is_recoverable error
    if b
    then ok (ParseOutcome.Success cursor ())
    else ok (ParseOutcome.Error error)
  | ParseOutcome.NeedMore => ok ParseOutcome.NeedMore) := by
  conv_lhs =>
    unfold Not.Insts.RusthammerParserInputTuple.parse_with DirectParser.parse_with
    dsimp only [Not.Insts.RusthammerParserInputTuple, Not.Insts.RusthammerEvalInputBackendTuple]
    unfold Not.Insts.RusthammerEvalInputBackendTuple.eval
  try simp only [dependent_examples.count_parser, record_example.record_header, bind_ok]
  direct_equation

theorem DirectRun.repeat_parse_eq {P : Type} {Q : Type} {Clause0_Output : Type} (ParserInst : DirectParser P
  Clause0_Output) (ParserInst1 : DirectParser Q Clause0_Output) (parser : P)
  (following : Q) (count : Std.Usize) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  DirectRun.repeat_parse ParserInst ParserInst1 parser following count input cursor context = (do
  if count = 0#usize
  then ParserInst.parse_with parser input cursor context
  else ParserInst1.parse_with following input cursor context) := by
  conv_lhs =>
    unfold DirectRun.repeat_parse RustHammer.Code.repeat_parse
  direct_equation

theorem DirectRun.repeat_run_eq {P : Type} {A : Type} {Clause0_Output : Type} {Clause1_Output : Type}
  (ParserInst : DirectParser P Clause0_Output) (RepeatAccumulatorInst :
  RepeatAccumulator A Clause0_Output Clause1_Output) (parser : P)
  (bounds : RepeatBounds) (accumulator : A) (input : Slice Std.U8)
  (cursor : Cursor) (context : ParseContext) :
  DirectRun.repeat_run ParserInst RepeatAccumulatorInst parser bounds accumulator input cursor context = (do
  DirectRun.repeat_run_with ParserInst ParserInst RepeatAccumulatorInst parser parser
    bounds accumulator input cursor context) := by
  conv_lhs =>
    unfold DirectRun.repeat_run RustHammer.Code.repeat_run
  direct_equation

theorem DirectRun.repeat_run_with_eq {P : Type} {Q : Type} {A : Type} {Clause0_Output : Type} {Clause2_Output :
  Type} (ParserInst : DirectParser P Clause0_Output) (ParserInst1 : DirectParser Q
  Clause0_Output) (RepeatAccumulatorInst : RepeatAccumulator A Clause0_Output
  Clause2_Output) (parser : P) (following : Q) (bounds : RepeatBounds)
  (accumulator : A) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  DirectRun.repeat_run_with ParserInst ParserInst1 RepeatAccumulatorInst parser following bounds accumulator input cursor context = (do
  let unbounded := core.option.Option.is_none bounds.max
  let r ← repeat_start input cursor unbounded
  match r with
  | core.result.Result.Ok _ =>
    let values ← RepeatAccumulatorInst.init accumulator
    DirectRun.repeat_run_with_loop ParserInst ParserInst1 RepeatAccumulatorInst parser
      following bounds.min bounds.max accumulator input context unbounded
      values cursor 0#usize
  | core.result.Result.Err error => ok (ParseOutcome.Error error)) := by
  conv_lhs =>
    unfold DirectRun.repeat_run_with RustHammer.Code.repeat_run_with
  direct_equation

theorem DirectRun.restrict_match_eq {P : Type} {Q : Type} {Clause0_Output : Type} {Clause1_Output : Type}
  (ParserInst : DirectParser P Clause0_Output) (ParserInst1 : DirectParser Q
  Clause1_Output) (first : P) (second : Q) (input : Slice Std.U8)
  (cursor : Cursor) (context : ParseContext) (allow_equal : Bool) :
  DirectRun.restrict_match ParserInst ParserInst1 first second input cursor context allow_equal = (do
  let po ← ParserInst.parse_with first input cursor context
  match po with
  | ParseOutcome.Success next _ =>
    let po1 ← ParserInst1.parse_with second input cursor context
    match po1 with
    | ParseOutcome.Success other _ =>
      let b ← match_length_allows next other allow_equal
      if b
      then ok po
      else ok (ParseOutcome.Error ParseError.Mismatch)
    | ParseOutcome.Error error =>
      let b ← ParseError.is_recoverable error
      if b
      then ok po
      else ok (ParseOutcome.Error error)
    | ParseOutcome.NeedMore => ok ParseOutcome.NeedMore
  | ParseOutcome.Error _ => ok po
  | ParseOutcome.NeedMore => ok ParseOutcome.NeedMore) := by
  conv_lhs =>
    unfold DirectRun.restrict_match RustHammer.Code.restrict_match
  direct_equation

theorem DirectRun.record_example.parse_record_body_eq (input : Slice Std.U8) (cursor : Cursor) (version : Std.U64)
  (flags : Std.U64) (count : Std.Usize) (context : ParseContext) :
  DirectRun.record_example.parse_record_body input cursor version flags count context = (do
  let po ←
    Seq.Insts.RusthammerParserInputPair.parse_with
      TakeAligned.Insts.RusthammerParserInputSharedInputSliceU8
      End.Insts.RusthammerParserInputTuple { first := { count }, second := () }
      input cursor context
  match po with
  | ParseOutcome.Success «end» p =>
    let (payload, _) := p
    ok (ParseOutcome.Success «end» { version, flags, payload })
  | ParseOutcome.Error error => ok (ParseOutcome.Error error)
  | ParseOutcome.NeedMore => ok ParseOutcome.NeedMore) := by
  conv_lhs =>
    unfold DirectRun.record_example.parse_record_body RustHammer.Code.record_example.parse_record_body
  direct_equation

theorem DirectRun.match_byte_pattern_eq (pattern : Slice Std.U8) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  DirectRun.match_byte_pattern pattern input cursor context = (do
  DirectRun.match_byte_pattern_loop pattern input context cursor 0#usize) := by
  conv_lhs =>
    unfold DirectRun.match_byte_pattern RustHammer.Code.match_byte_pattern
  direct_equation

end RustHammer.Code
