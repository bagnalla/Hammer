import RustHammer.DirectState

open RustHammer.Code.grammar.bytes
  RustHammer.Code.grammar.control
  RustHammer.Code.grammar.numeric
  RustHammer.Code.grammar.order
  RustHammer.Code.grammar.position
  RustHammer.Code.grammar.repeat
  RustHammer.Code.grammar.sequence
  RustHammer.Code.grammar.transform
  RustHammer.Code.input_types
  RustHammer.Code.parser_traits

/-! Proof-facing names for direct execution of the extracted evaluators.
Each parser definition delegates to `DirectParser.parse_with`; the helper
definitions project the empty backend state in the same way. Retaining these
names keeps grammar contracts readable independently of Aeneas's state-passing
representation. The lift lemmas are proved equalities, not assumed models.

Keep the projection functions as `def`: making them reducible would let the
inverse `direct_lift` rewrites repeatedly expose and rewrite their own bodies. -/

open Aeneas Aeneas.Std Result
namespace RustHammer.Code

abbrev grammar.numeric.Bits.Insts.RusthammerParserInputU64 : DirectParser Bits Std.U64 :=
  Bits.Insts.RusthammerParser_traitsEvalInputBackendU64 Direct

def grammar.numeric.Bits.Insts.RusthammerParserInputU64.parse_with (self : Bits) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome Std.U64) :=
  DirectParser.parse_with (Bits.Insts.RusthammerParserInputU64 ) self input cursor context

abbrev dependent_examples.CountPrefix.Insts.RusthammerParserInputUsize :
  DirectParser dependent_examples.CountPrefix Std.Usize :=
  dependent_examples.CountPrefix.Insts.RusthammerParser_traitsEvalInputBackendUsize Direct

def dependent_examples.CountPrefix.Insts.RusthammerParserInputUsize.parse_with (self : dependent_examples.CountPrefix) (input : Slice Std.U8)
  (cursor : Cursor) (context : ParseContext) :
  Result (ParseOutcome Std.Usize) :=
  DirectParser.parse_with (dependent_examples.CountPrefix.Insts.RusthammerParserInputUsize ) self input cursor context

abbrev grammar.bytes.TakeAligned.Insts.RusthammerParserInputSharedInputSliceU8 : DirectParser
  TakeAligned (Slice Std.U8) :=
  TakeAligned.Insts.RusthammerParser_traitsEvalInputBackendSharedSliceU8 Direct

def grammar.bytes.TakeAligned.Insts.RusthammerParserInputSharedInputSliceU8.parse_with (self : TakeAligned) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome (Slice Std.U8)) :=
  DirectParser.parse_with (TakeAligned.Insts.RusthammerParserInputSharedInputSliceU8 ) self input cursor context

abbrev grammar.repeat.Repeat.Insts.RusthammerParserInputVec {P : Type} {Clause0_Output :
  Type} (ParserInst : DirectParser P Clause0_Output) : DirectParser (Repeat P)
  (alloc.vec.Vec Clause0_Output) :=
  Repeat.Insts.RusthammerParser_traitsEvalInputBackendVec ParserInst

def grammar.repeat.Repeat.Insts.RusthammerParserInputVec.parse_with {P : Type} {Clause0_Output : Type} (ParserInst : DirectParser P Clause0_Output)
  (self : Repeat P) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome (alloc.vec.Vec Clause0_Output)) :=
  DirectParser.parse_with (Repeat.Insts.RusthammerParserInputVec ParserInst) self input cursor context

abbrev grammar.transform.Map.Insts.RusthammerParser {P : Type} {F : Type} {O : Type}
  {Clause0_Output : Type} (ParserInst : DirectParser P Clause0_Output)
  (coreopsfunctionFnFTupleClause0_OutputOInst : core.ops.function.Fn F
  Clause0_Output O) : DirectParser (Map P F) O :=
  Map.Insts.RusthammerParser_traitsEval ParserInst coreopsfunctionFnFTupleClause0_OutputOInst

def grammar.transform.Map.Insts.RusthammerParser.parse_with {P : Type} {F : Type} {O : Type} {Clause0_Output : Type} (ParserInst : DirectParser
  P Clause0_Output) (coreopsfunctionFnFTupleClause0_OutputOInst :
  core.ops.function.Fn F Clause0_Output O) (self : Map P F)
  (input : Slice Std.U8) (cursor : Cursor) (context : ParseContext) :
  Result (ParseOutcome O) :=
  DirectParser.parse_with (Map.Insts.RusthammerParser ParserInst coreopsfunctionFnFTupleClause0_OutputOInst) self input cursor context

abbrev grammar.sequence.Seq.Insts.RusthammerParserInputPair {P : Type} {Q : Type}
  {Clause0_Output : Type} {Clause1_Output : Type} (ParserInst : DirectParser P
  Clause0_Output) (ParserInst1 : DirectParser Q Clause1_Output) : DirectParser (Seq P Q)
  (Clause0_Output × Clause1_Output) :=
  Seq.Insts.RusthammerParser_traitsEvalInputBackendPair ParserInst ParserInst1

def grammar.sequence.Seq.Insts.RusthammerParserInputPair.parse_with {P : Type} {Q : Type} {Clause0_Output : Type} {Clause1_Output : Type}
  (ParserInst : DirectParser P Clause0_Output) (ParserInst1 : DirectParser Q
  Clause1_Output) (self : Seq P Q) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome (Clause0_Output × Clause1_Output)) :=
  DirectParser.parse_with (Seq.Insts.RusthammerParserInputPair ParserInst ParserInst1) self input cursor context

abbrev grammar.numeric.Bit.Insts.RusthammerParserInputBool : DirectParser Bit Bool :=
  Bit.Insts.RusthammerParser_traitsEvalInputBackendBool Direct

def grammar.numeric.Bit.Insts.RusthammerParserInputBool.parse_with (self : Bit) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome Bool) :=
  DirectParser.parse_with (Bit.Insts.RusthammerParserInputBool ) self input cursor context

abbrev grammar.control.Choice.Insts.RusthammerParser {P : Type} {Q : Type} {Clause0_Output :
  Type} (ParserInst : DirectParser P Clause0_Output) (ParserInst1 : DirectParser Q
  Clause0_Output) : DirectParser (Choice P Q) Clause0_Output :=
  Choice.Insts.RusthammerParser_traitsEval ParserInst ParserInst1

def grammar.control.Choice.Insts.RusthammerParser.parse_with {P : Type} {Q : Type} {Clause0_Output : Type} (ParserInst : DirectParser P
  Clause0_Output) (ParserInst1 : DirectParser Q Clause0_Output) (self : Choice P Q)
  (input : Slice Std.U8) (cursor : Cursor) (context : ParseContext) :
  Result (ParseOutcome Clause0_Output) :=
  DirectParser.parse_with (Choice.Insts.RusthammerParser ParserInst ParserInst1) self input cursor context

abbrev grammar.position.End.Insts.RusthammerParserInputTuple : DirectParser End Unit :=
  End.Insts.RusthammerParser_traitsEvalInputBackendTuple Direct

def grammar.position.End.Insts.RusthammerParserInputTuple.parse_with (self : End) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome Unit) :=
  DirectParser.parse_with (End.Insts.RusthammerParserInputTuple ) self input cursor context

abbrev grammar.numeric.Literal.Insts.RusthammerParserInputU64 : DirectParser Literal Std.U64 :=
  Literal.Insts.RusthammerParser_traitsEvalInputBackendU64 Direct

def grammar.numeric.Literal.Insts.RusthammerParserInputU64.parse_with (self : Literal) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome Std.U64) :=
  DirectParser.parse_with (Literal.Insts.RusthammerParserInputU64 ) self input cursor context

abbrev marker_example.Marker.Insts.RusthammerParserInputU64 : DirectParser
  marker_example.Marker Std.U64 :=
  marker_example.Marker.Insts.RusthammerParser_traitsEvalInputBackendU64 Direct

def marker_example.Marker.Insts.RusthammerParserInputU64.parse_with (self : marker_example.Marker) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome Std.U64) :=
  DirectParser.parse_with (marker_example.Marker.Insts.RusthammerParserInputU64 ) self input cursor context

abbrev record_example.RecordParser.Insts.RusthammerParserInputRecord : DirectParser
  record_example.RecordParser record_example.Record :=
  record_example.RecordParser.Insts.RusthammerParser_traitsEvalInputBackendRecord Direct

def record_example.RecordParser.Insts.RusthammerParserInputRecord.parse_with (self : record_example.RecordParser) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome record_example.Record) :=
  DirectParser.parse_with (record_example.RecordParser.Insts.RusthammerParserInputRecord ) self input cursor context

abbrev grammar.position.SkipBits.Insts.RusthammerParserInputTuple : DirectParser SkipBits Unit :=
  SkipBits.Insts.RusthammerParser_traitsEvalInputBackendTuple Direct

def grammar.position.SkipBits.Insts.RusthammerParserInputTuple.parse_with (self : SkipBits) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome Unit) :=
  DirectParser.parse_with (SkipBits.Insts.RusthammerParserInputTuple ) self input cursor context

abbrev grammar.position.Tell.Insts.RusthammerParserInputCursor : DirectParser Tell Cursor :=
  Tell.Insts.RusthammerParser_traitsEvalInputBackendCursor Direct

def grammar.position.Tell.Insts.RusthammerParserInputCursor.parse_with (self : Tell) (input : Slice Std.U8) (cursor : Cursor)
  (_context : ParseContext) :
  Result (ParseOutcome Cursor) :=
  DirectParser.parse_with (Tell.Insts.RusthammerParserInputCursor ) self input cursor _context

abbrev Shared0P.Insts.RusthammerParser {P : Type} {Clause0_Output : Type}
  (ParserInst : DirectParser P Clause0_Output) : DirectParser P Clause0_Output :=
  Shared0P.Insts.RusthammerParser_traitsEval ParserInst

def Shared0P.Insts.RusthammerParser.parse_with {P : Type} {Clause0_Output : Type} (ParserInst : DirectParser P Clause0_Output)
  (self : P) (input : Slice Std.U8) (cursor : Cursor) (context : ParseContext)
  :
  Result (ParseOutcome Clause0_Output) :=
  DirectParser.parse_with (Shared0P.Insts.RusthammerParser ParserInst) self input cursor context

def Shared0P.Insts.RusthammerParser.parse   {P : Type} {Clause0_Output : Type} (ParserInst : DirectParser P Clause0_Output)
  (self : P) (input : Slice Std.U8) (cursor : Cursor) :
  Result (core.result.Result (Cursor × Clause0_Output) ParseError) :=
  DirectParser.parse (Shared0P.Insts.RusthammerParser ParserInst) self input cursor

abbrev grammar.order.WithOrder.Insts.RusthammerParser {P : Type} {Clause0_Output : Type}
  (ParserInst : DirectParser P Clause0_Output) : DirectParser (WithOrder P) Clause0_Output :=
  WithOrder.Insts.RusthammerParser_traitsEval ParserInst

def grammar.order.WithOrder.Insts.RusthammerParser.parse_with {P : Type} {Clause0_Output : Type} (ParserInst : DirectParser P Clause0_Output)
  (self : WithOrder P) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome Clause0_Output) :=
  DirectParser.parse_with (WithOrder.Insts.RusthammerParser ParserInst) self input cursor context

abbrev grammar.numeric.SignedBits.Insts.RusthammerParserInputI64 : DirectParser SignedBits Std.I64 :=
  SignedBits.Insts.RusthammerParser_traitsEvalInputBackendI64 Direct

def grammar.numeric.SignedBits.Insts.RusthammerParserInputI64.parse_with (self : SignedBits) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome Std.I64) :=
  DirectParser.parse_with (SignedBits.Insts.RusthammerParserInputI64 ) self input cursor context

abbrev grammar.numeric.Byte.Insts.RusthammerParserInputU8 : DirectParser Code.grammar.numeric.Byte Std.U8 :=
  Code.grammar.numeric.Byte.Insts.RusthammerParser_traitsEvalInputBackendU8 Direct

def grammar.numeric.Byte.Insts.RusthammerParserInputU8.parse_with (self : Code.grammar.numeric.Byte) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome Std.U8) :=
  DirectParser.parse_with (Code.grammar.numeric.Byte.Insts.RusthammerParserInputU8 ) self input cursor context

abbrev grammar.numeric.BeU16.Insts.RusthammerParserInputU16 : DirectParser BeU16 Std.U16 :=
  BeU16.Insts.RusthammerParser_traitsEvalInputBackendU16 Direct

def grammar.numeric.BeU16.Insts.RusthammerParserInputU16.parse_with (self : BeU16) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome Std.U16) :=
  DirectParser.parse_with (BeU16.Insts.RusthammerParserInputU16 ) self input cursor context

abbrev grammar.numeric.BeU32.Insts.RusthammerParserInputU32 : DirectParser BeU32 Std.U32 :=
  BeU32.Insts.RusthammerParser_traitsEvalInputBackendU32 Direct

def grammar.numeric.BeU32.Insts.RusthammerParserInputU32.parse_with (self : BeU32) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome Std.U32) :=
  DirectParser.parse_with (BeU32.Insts.RusthammerParserInputU32 ) self input cursor context

abbrev grammar.numeric.BeU64.Insts.RusthammerParserInputU64 : DirectParser BeU64 Std.U64 :=
  BeU64.Insts.RusthammerParser_traitsEvalInputBackendU64 Direct

def grammar.numeric.BeU64.Insts.RusthammerParserInputU64.parse_with (self : BeU64) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome Std.U64) :=
  DirectParser.parse_with (BeU64.Insts.RusthammerParserInputU64 ) self input cursor context

abbrev grammar.numeric.I8.Insts.RusthammerParserInputI8 : DirectParser Code.grammar.numeric.I8 Std.I8 :=
  Code.grammar.numeric.I8.Insts.RusthammerParser_traitsEvalInputBackendI8 Direct

def grammar.numeric.I8.Insts.RusthammerParserInputI8.parse_with (self : Code.grammar.numeric.I8) (input : Slice Std.U8) (cursor : Cursor) (context : ParseContext)
  :
  Result (ParseOutcome Std.I8) :=
  DirectParser.parse_with (Code.grammar.numeric.I8.Insts.RusthammerParserInputI8 ) self input cursor context

abbrev grammar.numeric.BeI16.Insts.RusthammerParserInputI16 : DirectParser BeI16 Std.I16 :=
  BeI16.Insts.RusthammerParser_traitsEvalInputBackendI16 Direct

def grammar.numeric.BeI16.Insts.RusthammerParserInputI16.parse_with (self : BeI16) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome Std.I16) :=
  DirectParser.parse_with (BeI16.Insts.RusthammerParserInputI16 ) self input cursor context

abbrev grammar.numeric.BeI32.Insts.RusthammerParserInputI32 : DirectParser BeI32 Std.I32 :=
  BeI32.Insts.RusthammerParser_traitsEvalInputBackendI32 Direct

def grammar.numeric.BeI32.Insts.RusthammerParserInputI32.parse_with (self : BeI32) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome Std.I32) :=
  DirectParser.parse_with (BeI32.Insts.RusthammerParserInputI32 ) self input cursor context

abbrev grammar.numeric.BeI64.Insts.RusthammerParserInputI64 : DirectParser BeI64 Std.I64 :=
  BeI64.Insts.RusthammerParser_traitsEvalInputBackendI64 Direct

def grammar.numeric.BeI64.Insts.RusthammerParserInputI64.parse_with (self : BeI64) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome Std.I64) :=
  DirectParser.parse_with (BeI64.Insts.RusthammerParserInputI64 ) self input cursor context

abbrev grammar.bytes.ByteIn.Insts.RusthammerParserInputU8 : DirectParser ByteIn Std.U8 :=
  ByteIn.Insts.RusthammerParser_traitsEvalInputBackendU8 Direct

def grammar.bytes.ByteIn.Insts.RusthammerParserInputU8.parse_with (self : ByteIn) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome Std.U8) :=
  DirectParser.parse_with (ByteIn.Insts.RusthammerParserInputU8 ) self input cursor context

abbrev grammar.bytes.ByteNotIn.Insts.RusthammerParserInputU8 : DirectParser ByteNotIn Std.U8 :=
  ByteNotIn.Insts.RusthammerParser_traitsEvalInputBackendU8 Direct

def grammar.bytes.ByteNotIn.Insts.RusthammerParserInputU8.parse_with (self : ByteNotIn) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome Std.U8) :=
  DirectParser.parse_with (ByteNotIn.Insts.RusthammerParserInputU8 ) self input cursor context

abbrev grammar.bytes.BytePattern.Insts.RusthammerParserInputSharedPatternSliceU8 : DirectParser
  BytePattern (Slice Std.U8) :=
  BytePattern.Insts.RusthammerParser_traitsEvalInputBackendSharedSliceU8 Direct

def grammar.bytes.BytePattern.Insts.RusthammerParserInputSharedPatternSliceU8.parse_with (self : BytePattern) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome (Slice Std.U8)) :=
  DirectParser.parse_with (BytePattern.Insts.RusthammerParserInputSharedPatternSliceU8 ) self input cursor context

abbrev grammar.control.Epsilon.Insts.RusthammerParserInputTuple : DirectParser Epsilon Unit :=
  Epsilon.Insts.RusthammerParser_traitsEvalInputBackendTuple Direct

def grammar.control.Epsilon.Insts.RusthammerParserInputTuple.parse_with (self : Epsilon) (s : Slice Std.U8) (cursor : Cursor) (pc : ParseContext) :
  Result (ParseOutcome Unit) :=
  DirectParser.parse_with (Epsilon.Insts.RusthammerParserInputTuple ) self s cursor pc

abbrev grammar.control.Fail.Insts.RusthammerParser (T : Type) : DirectParser (Fail T) T :=
  Fail.Insts.RusthammerParser_traitsEval Direct T

def grammar.control.Fail.Insts.RusthammerParser.parse_with {T : Type} (self : Fail T) (s : Slice Std.U8) (c : Cursor)
  (pc : ParseContext) :
  Result (ParseOutcome T) :=
  DirectParser.parse_with (Fail.Insts.RusthammerParser T) self s c pc

abbrev grammar.sequence.Bind.Insts.RusthammerParser {P : Type} {F : Type} {Q : Type}
  {Clause0_Output : Type} {Clause2_Output : Type} (ParserInst : DirectParser P
  Clause0_Output) (coreopsfunctionFnFTupleClause0_OutputQInst :
  core.ops.function.Fn F Clause0_Output Q) (ParserInst1 : DirectParser Q
  Clause2_Output) : DirectParser (Bind P F) Clause2_Output :=
  Bind.Insts.RusthammerParser_traitsEval ParserInst coreopsfunctionFnFTupleClause0_OutputQInst ParserInst1

def grammar.sequence.Bind.Insts.RusthammerParser.parse_with {P : Type} {F : Type} {Q : Type} {Clause0_Output : Type} {Clause2_Output :
  Type} (ParserInst : DirectParser P Clause0_Output)
  (coreopsfunctionFnFTupleClause0_OutputQInst : core.ops.function.Fn F
  Clause0_Output Q) (ParserInst1 : DirectParser Q Clause2_Output) (self : Bind P F)
  (input : Slice Std.U8) (cursor : Cursor) (context : ParseContext) :
  Result (ParseOutcome Clause2_Output) :=
  DirectParser.parse_with (Bind.Insts.RusthammerParser ParserInst coreopsfunctionFnFTupleClause0_OutputQInst ParserInst1) self input cursor context

abbrev grammar.sequence.Left.Insts.RusthammerParser {P : Type} {Q : Type} {Clause0_Output :
  Type} {Clause1_Output : Type} (ParserInst : DirectParser P Clause0_Output)
  (ParserInst1 : DirectParser Q Clause1_Output) : DirectParser (Left P Q) Clause0_Output :=
  Left.Insts.RusthammerParser_traitsEval ParserInst ParserInst1

def grammar.sequence.Left.Insts.RusthammerParser.parse_with {P : Type} {Q : Type} {Clause0_Output : Type} {Clause1_Output : Type}
  (ParserInst : DirectParser P Clause0_Output) (ParserInst1 : DirectParser Q
  Clause1_Output) (self : Left P Q) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome Clause0_Output) :=
  DirectParser.parse_with (Left.Insts.RusthammerParser ParserInst ParserInst1) self input cursor context

abbrev grammar.sequence.Right.Insts.RusthammerParser {P : Type} {Q : Type} {Clause0_Output :
  Type} {Clause1_Output : Type} (ParserInst : DirectParser P Clause0_Output)
  (ParserInst1 : DirectParser Q Clause1_Output) : DirectParser (Right P Q) Clause1_Output :=
  Right.Insts.RusthammerParser_traitsEval ParserInst ParserInst1

def grammar.sequence.Right.Insts.RusthammerParser.parse_with {P : Type} {Q : Type} {Clause0_Output : Type} {Clause1_Output : Type}
  (ParserInst : DirectParser P Clause0_Output) (ParserInst1 : DirectParser Q
  Clause1_Output) (self : Right P Q) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome Clause1_Output) :=
  DirectParser.parse_with (Right.Insts.RusthammerParser ParserInst ParserInst1) self input cursor context

abbrev grammar.sequence.Middle.Insts.RusthammerParser {L : Type} {P : Type} {R : Type}
  {Clause0_Output : Type} {Clause1_Output : Type} {Clause2_Output : Type}
  (ParserInst : DirectParser L Clause0_Output) (ParserInst1 : DirectParser P
  Clause1_Output) (ParserInst2 : DirectParser R Clause2_Output) : DirectParser (Middle L P
  R) Clause1_Output :=
  Middle.Insts.RusthammerParser_traitsEval ParserInst ParserInst1 ParserInst2

def grammar.sequence.Middle.Insts.RusthammerParser.parse_with {L : Type} {P : Type} {R : Type} {Clause0_Output : Type} {Clause1_Output :
  Type} {Clause2_Output : Type} (ParserInst : DirectParser L Clause0_Output)
  (ParserInst1 : DirectParser P Clause1_Output) (ParserInst2 : DirectParser R
  Clause2_Output) (self : Middle L P R) (input : Slice Std.U8)
  (cursor : Cursor) (context : ParseContext) :
  Result (ParseOutcome Clause1_Output) :=
  DirectParser.parse_with (Middle.Insts.RusthammerParser ParserInst ParserInst1 ParserInst2) self input cursor context

abbrev grammar.sequence.Ignore.Insts.RusthammerParserInputTuple {P : Type} {Clause0_Output :
  Type} (ParserInst : DirectParser P Clause0_Output) : DirectParser (Ignore P) Unit :=
  Ignore.Insts.RusthammerParser_traitsEvalInputBackendTuple ParserInst

def grammar.sequence.Ignore.Insts.RusthammerParserInputTuple.parse_with {P : Type} {Clause0_Output : Type} (ParserInst : DirectParser P Clause0_Output)
  (self : Ignore P) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome Unit) :=
  DirectParser.parse_with (Ignore.Insts.RusthammerParserInputTuple ParserInst) self input cursor context

abbrev grammar.repeat.FoldRepeat.Insts.RusthammerParser {P : Type} {I : Type} {F : Type} {R
  : Type} {Clause0_Output : Type} (ParserInst : DirectParser P Clause0_Output)
  (coreopsfunctionFnITupleRInst : core.ops.function.Fn I Unit R)
  (coreopsfunctionFnFPairRInst : core.ops.function.Fn F (R × Clause0_Output)
  R) : DirectParser (FoldRepeat P I F) R :=
  FoldRepeat.Insts.RusthammerParser_traitsEval ParserInst coreopsfunctionFnITupleRInst coreopsfunctionFnFPairRInst

def grammar.repeat.FoldRepeat.Insts.RusthammerParser.parse_with {P : Type} {I : Type} {F : Type} {R : Type} {Clause0_Output : Type}
  (ParserInst : DirectParser P Clause0_Output) (coreopsfunctionFnITupleRInst :
  core.ops.function.Fn I Unit R) (coreopsfunctionFnFPairRInst :
  core.ops.function.Fn F (R × Clause0_Output) R) (self : FoldRepeat P I F)
  (input : Slice Std.U8) (cursor : Cursor) (context : ParseContext) :
  Result (ParseOutcome R) :=
  DirectParser.parse_with (FoldRepeat.Insts.RusthammerParser ParserInst coreopsfunctionFnITupleRInst coreopsfunctionFnFPairRInst) self input cursor context

abbrev grammar.repeat.SepBy.Insts.RusthammerParserInputVec {P : Type} {S : Type}
  {Clause0_Output : Type} {Clause1_Output : Type} (ParserInst : DirectParser P
  Clause0_Output) (ParserInst1 : DirectParser S Clause1_Output) : DirectParser (SepBy P S)
  (alloc.vec.Vec Clause0_Output) :=
  SepBy.Insts.RusthammerParser_traitsEvalInputBackendVec ParserInst ParserInst1

def grammar.repeat.SepBy.Insts.RusthammerParserInputVec.parse_with {P : Type} {S : Type} {Clause0_Output : Type} {Clause1_Output : Type}
  (ParserInst : DirectParser P Clause0_Output) (ParserInst1 : DirectParser S
  Clause1_Output) (self : SepBy P S) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome (alloc.vec.Vec Clause0_Output)) :=
  DirectParser.parse_with (SepBy.Insts.RusthammerParserInputVec ParserInst ParserInst1) self input cursor context

abbrev grammar.repeat.FoldSepBy.Insts.RusthammerParser {P : Type} {S : Type} {I : Type} {F :
  Type} {R : Type} {Clause0_Output : Type} {Clause1_Output : Type} (ParserInst
  : DirectParser P Clause0_Output) (ParserInst1 : DirectParser S Clause1_Output)
  (coreopsfunctionFnITupleRInst : core.ops.function.Fn I Unit R)
  (coreopsfunctionFnFPairRInst : core.ops.function.Fn F (R × Clause0_Output)
  R) : DirectParser (FoldSepBy P S I F) R :=
  FoldSepBy.Insts.RusthammerParser_traitsEval ParserInst ParserInst1 coreopsfunctionFnITupleRInst coreopsfunctionFnFPairRInst

def grammar.repeat.FoldSepBy.Insts.RusthammerParser.parse_with {P : Type} {S : Type} {I : Type} {F : Type} {R : Type} {Clause0_Output :
  Type} {Clause1_Output : Type} (ParserInst : DirectParser P Clause0_Output)
  (ParserInst1 : DirectParser S Clause1_Output) (coreopsfunctionFnITupleRInst :
  core.ops.function.Fn I Unit R) (coreopsfunctionFnFPairRInst :
  core.ops.function.Fn F (R × Clause0_Output) R) (self : FoldSepBy P S I F)
  (input : Slice Std.U8) (cursor : Cursor) (context : ParseContext) :
  Result (ParseOutcome R) :=
  DirectParser.parse_with (FoldSepBy.Insts.RusthammerParser ParserInst ParserInst1 coreopsfunctionFnITupleRInst coreopsfunctionFnFPairRInst) self input cursor context

abbrev grammar.transform.TryMap.Insts.RusthammerParser {P : Type} {F : Type} {O : Type} {E :
  Type} {Clause0_Output : Type} (ParserInst : DirectParser P Clause0_Output)
  (coreopsfunctionFnFTupleClause0_OutputResultInst : core.ops.function.Fn F
  Clause0_Output (core.result.Result O E)) : DirectParser (TryMap P F) O :=
  TryMap.Insts.RusthammerParser_traitsEval ParserInst coreopsfunctionFnFTupleClause0_OutputResultInst

def grammar.transform.TryMap.Insts.RusthammerParser.parse_with {P : Type} {F : Type} {O : Type} {E : Type} {Clause0_Output : Type}
  (ParserInst : DirectParser P Clause0_Output)
  (coreopsfunctionFnFTupleClause0_OutputResultInst : core.ops.function.Fn F
  Clause0_Output (core.result.Result O E)) (self : TryMap P F)
  (input : Slice Std.U8) (cursor : Cursor) (context : ParseContext) :
  Result (ParseOutcome O) :=
  DirectParser.parse_with (TryMap.Insts.RusthammerParser ParserInst coreopsfunctionFnFTupleClause0_OutputResultInst) self input cursor context

abbrev grammar.transform.Verify.Insts.RusthammerParser {P : Type} {F : Type} {Clause0_Output :
  Type} (ParserInst : DirectParser P Clause0_Output)
  (coreopsfunctionFnFTupleSharedInputClause0_OutputBoolInst :
  core.ops.function.Fn F Clause0_Output Bool) : DirectParser (Verify P F)
  Clause0_Output :=
  Verify.Insts.RusthammerParser_traitsEval ParserInst coreopsfunctionFnFTupleSharedInputClause0_OutputBoolInst

def grammar.transform.Verify.Insts.RusthammerParser.parse_with {P : Type} {F : Type} {Clause0_Output : Type} (ParserInst : DirectParser P
  Clause0_Output) (coreopsfunctionFnFTupleSharedInputClause0_OutputBoolInst :
  core.ops.function.Fn F Clause0_Output Bool) (self : Verify P F)
  (input : Slice Std.U8) (cursor : Cursor) (context : ParseContext) :
  Result (ParseOutcome Clause0_Output) :=
  DirectParser.parse_with (Verify.Insts.RusthammerParser ParserInst coreopsfunctionFnFTupleSharedInputClause0_OutputBoolInst) self input cursor context

abbrev grammar.transform.IntRange.Insts.RusthammerParser {P : Type} {T : Type} (ParserInst :
  DirectParser P T) (corecmpOrdInst : core.cmp.Ord T) : DirectParser (IntRange P T) T :=
  IntRange.Insts.RusthammerParser_traitsEval ParserInst corecmpOrdInst

def grammar.transform.IntRange.Insts.RusthammerParser.parse_with {P : Type} {T : Type} (ParserInst : DirectParser P T) (corecmpOrdInst :
  core.cmp.Ord T) (self : IntRange P T) (input : Slice Std.U8)
  (cursor : Cursor) (context : ParseContext) :
  Result (ParseOutcome T) :=
  DirectParser.parse_with (IntRange.Insts.RusthammerParser ParserInst corecmpOrdInst) self input cursor context

abbrev grammar.control.ButNot.Insts.RusthammerParser {P : Type} {Q : Type} {Clause0_Output :
  Type} {Clause1_Output : Type} (ParserInst : DirectParser P Clause0_Output)
  (ParserInst1 : DirectParser Q Clause1_Output) : DirectParser (ButNot P Q) Clause0_Output :=
  ButNot.Insts.RusthammerParser_traitsEval ParserInst ParserInst1

def grammar.control.ButNot.Insts.RusthammerParser.parse_with {P : Type} {Q : Type} {Clause0_Output : Type} {Clause1_Output : Type}
  (ParserInst : DirectParser P Clause0_Output) (ParserInst1 : DirectParser Q
  Clause1_Output) (self : ButNot P Q) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome Clause0_Output) :=
  DirectParser.parse_with (ButNot.Insts.RusthammerParser ParserInst ParserInst1) self input cursor context

abbrev grammar.control.Difference.Insts.RusthammerParser {P : Type} {Q : Type}
  {Clause0_Output : Type} {Clause1_Output : Type} (ParserInst : DirectParser P
  Clause0_Output) (ParserInst1 : DirectParser Q Clause1_Output) : DirectParser (Difference
  P Q) Clause0_Output :=
  Difference.Insts.RusthammerParser_traitsEval ParserInst ParserInst1

def grammar.control.Difference.Insts.RusthammerParser.parse_with {P : Type} {Q : Type} {Clause0_Output : Type} {Clause1_Output : Type}
  (ParserInst : DirectParser P Clause0_Output) (ParserInst1 : DirectParser Q
  Clause1_Output) (self : Difference P Q) (input : Slice Std.U8)
  (cursor : Cursor) (context : ParseContext) :
  Result (ParseOutcome Clause0_Output) :=
  DirectParser.parse_with (Difference.Insts.RusthammerParser ParserInst ParserInst1) self input cursor context

abbrev grammar.control.Xor.Insts.RusthammerParser {P : Type} {Q : Type} {Clause0_Output :
  Type} (ParserInst : DirectParser P Clause0_Output) (ParserInst1 : DirectParser Q
  Clause0_Output) : DirectParser (Xor P Q) Clause0_Output :=
  Xor.Insts.RusthammerParser_traitsEval ParserInst ParserInst1

def grammar.control.Xor.Insts.RusthammerParser.parse_with {P : Type} {Q : Type} {Clause0_Output : Type} (ParserInst : DirectParser P
  Clause0_Output) (ParserInst1 : DirectParser Q Clause0_Output) (self : Xor P Q)
  (input : Slice Std.U8) (cursor : Cursor) (context : ParseContext) :
  Result (ParseOutcome Clause0_Output) :=
  DirectParser.parse_with (Xor.Insts.RusthammerParser ParserInst ParserInst1) self input cursor context

abbrev grammar.control.Optional.Insts.RusthammerParserInputOption {P : Type} {Clause0_Output
  : Type} (ParserInst : DirectParser P Clause0_Output) : DirectParser (Optional P) (Option
  Clause0_Output) :=
  Optional.Insts.RusthammerParser_traitsEvalInputBackendOption ParserInst

def grammar.control.Optional.Insts.RusthammerParserInputOption.parse_with {P : Type} {Clause0_Output : Type} (ParserInst : DirectParser P Clause0_Output)
  (self : Optional P) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome (Option Clause0_Output)) :=
  DirectParser.parse_with (Optional.Insts.RusthammerParserInputOption ParserInst) self input cursor context

abbrev grammar.control.And.Insts.RusthammerParserInputTuple {P : Type} {Clause0_Output :
  Type} (ParserInst : DirectParser P Clause0_Output) : DirectParser (And P) Unit :=
  And.Insts.RusthammerParser_traitsEvalInputBackendTuple ParserInst

def grammar.control.And.Insts.RusthammerParserInputTuple.parse_with {P : Type} {Clause0_Output : Type} (ParserInst : DirectParser P Clause0_Output)
  (self : And P) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome Unit) :=
  DirectParser.parse_with (And.Insts.RusthammerParserInputTuple ParserInst) self input cursor context

abbrev grammar.control.Not.Insts.RusthammerParserInputTuple {P : Type} {Clause0_Output :
  Type} (ParserInst : DirectParser P Clause0_Output) : DirectParser (Not P) Unit :=
  Not.Insts.RusthammerParser_traitsEvalInputBackendTuple ParserInst

def grammar.control.Not.Insts.RusthammerParserInputTuple.parse_with {P : Type} {Clause0_Output : Type} (ParserInst : DirectParser P Clause0_Output)
  (self : Not P) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome Unit) :=
  DirectParser.parse_with (Not.Insts.RusthammerParserInputTuple ParserInst) self input cursor context

def DirectRun.repeat_parse   {P : Type} {Q : Type} {Clause0_Output : Type} (ParserInst : DirectParser P
  Clause0_Output) (ParserInst1 : DirectParser Q Clause0_Output) (parser : P)
  (following : Q) (count : Std.Usize) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome Clause0_Output) := do
  let (outcome, _) ← RustHammer.Code.grammar.repeat.repeat_parse ParserInst ParserInst1 () parser following count input cursor context
  ok outcome

def DirectRun.repeat_run   {P : Type} {A : Type} {Clause0_Output : Type} {Clause1_Output : Type}
  (ParserInst : DirectParser P Clause0_Output) (RepeatAccumulatorInst :
  RepeatAccumulator A Clause0_Output Clause1_Output) (parser : P)
  (bounds : RepeatBounds) (accumulator : A) (input : Slice Std.U8)
  (cursor : Cursor) (context : ParseContext) :
  Result (ParseOutcome Clause1_Output) := do
  let (outcome, _) ← RustHammer.Code.grammar.repeat.repeat_run ParserInst RepeatAccumulatorInst () parser bounds accumulator input cursor context
  ok outcome

def DirectRun.repeat_run_with   {P : Type} {Q : Type} {A : Type} {Clause0_Output : Type} {Clause2_Output :
  Type} (ParserInst : DirectParser P Clause0_Output) (ParserInst1 : DirectParser Q
  Clause0_Output) (RepeatAccumulatorInst : RepeatAccumulator A Clause0_Output
  Clause2_Output) (parser : P) (following : Q) (bounds : RepeatBounds)
  (accumulator : A) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome Clause2_Output) := do
  let (outcome, _) ← RustHammer.Code.grammar.repeat.repeat_run_with ParserInst ParserInst1 RepeatAccumulatorInst () parser following bounds accumulator input cursor context
  ok outcome

def DirectRun.restrict_match   {P : Type} {Q : Type} {Clause0_Output : Type} {Clause1_Output : Type}
  (ParserInst : DirectParser P Clause0_Output) (ParserInst1 : DirectParser Q
  Clause1_Output) (first : P) (second : Q) (input : Slice Std.U8)
  (cursor : Cursor) (context : ParseContext) (allow_equal : Bool) :
  Result (ParseOutcome Clause0_Output) := do
  let (outcome, _) ← RustHammer.Code.grammar.control.restrict_match ParserInst ParserInst1 () first second input cursor context allow_equal
  ok outcome

def DirectRun.record_example.parse_record_body   (input : Slice Std.U8) (cursor : Cursor) (version : Std.U64)
  (flags : Std.U64) (count : Std.Usize) (context : ParseContext) :
  Result (ParseOutcome record_example.Record) := do
  let (outcome, _) ← RustHammer.Code.record_example.parse_record_body () input cursor version flags count context
  ok outcome

def DirectRun.match_byte_pattern   (pattern : Slice Std.U8) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome Unit) := do
  let (outcome, _) ← RustHammer.Code.grammar.bytes.match_byte_pattern () pattern input cursor context
  ok outcome

def DirectRun.repeat_run_with_loop   {P : Type} {Q : Type} {A : Type} {Clause0_Output : Type} {Clause2_Output :
  Type} (ParserInst : DirectParser P Clause0_Output) (ParserInst1 : DirectParser Q
  Clause0_Output) (RepeatAccumulatorInst : RepeatAccumulator A Clause0_Output
  Clause2_Output) (parser : P) (following : Q) (i : Std.Usize)
  (o : Option Std.Usize) (accumulator : A) (input : Slice Std.U8)
  (context : ParseContext) (unbounded : Bool) (values : Clause2_Output)
  (next : Cursor) (count : Std.Usize) :
  Result (ParseOutcome Clause2_Output) := do
  let (outcome, _) ← RustHammer.Code.grammar.repeat.repeat_run_with_loop ParserInst ParserInst1 RepeatAccumulatorInst () parser following i o accumulator input context unbounded values next count
  ok outcome

def DirectRun.match_byte_pattern_loop   (pattern : Slice Std.U8) (input : Slice Std.U8) (context : ParseContext)
  (next : Cursor) (index : Std.Usize) :
  Result (ParseOutcome Unit) := do
  let (outcome, _) ← RustHammer.Code.grammar.bytes.match_byte_pattern_loop () pattern input context next index
  ok outcome

-- Closure views retain the source-independent names used by the contracts.
abbrev dependent_examples.ParserInputCountPrefixUsize.parse_with.closure  :=
  dependent_examples.count_parser.closure

abbrev dependent_examples.ParserInputCountPrefixUsize.parse_with.closure.Insts.CoreOpsFunctionFnTupleU64ResultUsizeTuple.call   (c : dependent_examples.ParserInputCountPrefixUsize.parse_with.closure)
  (tupled_args : Std.U64) :
  Result (core.result.Result Std.Usize Unit) :=
  dependent_examples.count_parser.closure.Insts.CoreOpsFunctionFnTupleU64ResultUsizeTuple.call c tupled_args

abbrev dependent_examples.ParserInputCountPrefixUsize.parse_with.closure.Insts.CoreOpsFunctionFnMutTupleU64ResultUsizeTuple.call_mut   (state : dependent_examples.ParserInputCountPrefixUsize.parse_with.closure)
  (args : Std.U64) :
  Result ((core.result.Result Std.Usize Unit) ×
    dependent_examples.ParserInputCountPrefixUsize.parse_with.closure) :=
  dependent_examples.count_parser.closure.Insts.CoreOpsFunctionFnMutTupleU64ResultUsizeTuple.call_mut state args

abbrev dependent_examples.ParserInputCountPrefixUsize.parse_with.closure.Insts.CoreOpsFunctionFnOnceTupleU64ResultUsizeTuple.call_once   (c : dependent_examples.ParserInputCountPrefixUsize.parse_with.closure)
  (i : Std.U64) :
  Result (core.result.Result Std.Usize Unit) :=
  dependent_examples.count_parser.closure.Insts.CoreOpsFunctionFnOnceTupleU64ResultUsizeTuple.call_once c i

abbrev dependent_examples.ParserInputCountPrefixUsize.parse_with.closure.Insts.CoreOpsFunctionFnOnceTupleU64ResultUsizeTuple   : core.ops.function.FnOnce
  dependent_examples.ParserInputCountPrefixUsize.parse_with.closure Std.U64
  (core.result.Result Std.Usize Unit) :=
  dependent_examples.count_parser.closure.Insts.CoreOpsFunctionFnOnceTupleU64ResultUsizeTuple

abbrev dependent_examples.ParserInputCountPrefixUsize.parse_with.closure.Insts.CoreOpsFunctionFnMutTupleU64ResultUsizeTuple   : core.ops.function.FnMut
  dependent_examples.ParserInputCountPrefixUsize.parse_with.closure Std.U64
  (core.result.Result Std.Usize Unit) :=
  dependent_examples.count_parser.closure.Insts.CoreOpsFunctionFnMutTupleU64ResultUsizeTuple

abbrev dependent_examples.ParserInputCountPrefixUsize.parse_with.closure.Insts.CoreOpsFunctionFnTupleU64ResultUsizeTuple   : core.ops.function.Fn
  dependent_examples.ParserInputCountPrefixUsize.parse_with.closure Std.U64
  (core.result.Result Std.Usize Unit) :=
  dependent_examples.count_parser.closure.Insts.CoreOpsFunctionFnTupleU64ResultUsizeTuple

abbrev record_example.ParserInputRecordParserRecord.parse_with.closure  :=
  record_example.record_header.closure

abbrev record_example.ParserInputRecordParserRecord.parse_with.closure.Insts.CoreOpsFunctionFnTupleShared0PairU64PairU64U64Bool.call   (c : record_example.ParserInputRecordParserRecord.parse_with.closure)
  (tupled_args : (Std.U64 × (Std.U64 × Std.U64))) :
  Result Bool :=
  record_example.record_header.closure.Insts.CoreOpsFunctionFnTupleShared0PairU64PairU64U64Bool.call c tupled_args

abbrev record_example.ParserInputRecordParserRecord.parse_with.closure.Insts.CoreOpsFunctionFnMutTupleShared0PairU64PairU64U64Bool.call_mut   (state : record_example.ParserInputRecordParserRecord.parse_with.closure)
  (args : (Std.U64 × (Std.U64 × Std.U64))) :
  Result (Bool ×
    record_example.ParserInputRecordParserRecord.parse_with.closure) :=
  record_example.record_header.closure.Insts.CoreOpsFunctionFnMutTupleShared0PairU64PairU64U64Bool.call_mut state args

abbrev record_example.ParserInputRecordParserRecord.parse_with.closure.Insts.CoreOpsFunctionFnOnceTupleShared0PairU64PairU64U64Bool.call_once   (c : record_example.ParserInputRecordParserRecord.parse_with.closure)
  (p : (Std.U64 × (Std.U64 × Std.U64))) :
  Result Bool :=
  record_example.record_header.closure.Insts.CoreOpsFunctionFnOnceTupleShared0PairU64PairU64U64Bool.call_once c p

abbrev record_example.ParserInputRecordParserRecord.parse_with.closure.Insts.CoreOpsFunctionFnOnceTupleShared0PairU64PairU64U64Bool   : core.ops.function.FnOnce
  record_example.ParserInputRecordParserRecord.parse_with.closure (Std.U64 ×
  (Std.U64 × Std.U64)) Bool :=
  record_example.record_header.closure.Insts.CoreOpsFunctionFnOnceTupleShared0PairU64PairU64U64Bool

abbrev record_example.ParserInputRecordParserRecord.parse_with.closure.Insts.CoreOpsFunctionFnMutTupleShared0PairU64PairU64U64Bool   : core.ops.function.FnMut
  record_example.ParserInputRecordParserRecord.parse_with.closure (Std.U64 ×
  (Std.U64 × Std.U64)) Bool :=
  record_example.record_header.closure.Insts.CoreOpsFunctionFnMutTupleShared0PairU64PairU64U64Bool

abbrev record_example.ParserInputRecordParserRecord.parse_with.closure.Insts.CoreOpsFunctionFnTupleShared0PairU64PairU64U64Bool   : core.ops.function.Fn
  record_example.ParserInputRecordParserRecord.parse_with.closure (Std.U64 ×
  (Std.U64 × Std.U64)) Bool :=
  record_example.record_header.closure.Insts.CoreOpsFunctionFnTupleShared0PairU64PairU64U64Bool

abbrev ParserInputByteInU8.parse_with.closure  :=
  EvalInputByteInBackendU8.eval.closure Direct

abbrev ParserInputByteInU8.parse_with.closure.Insts.CoreOpsFunctionFnTupleShared1U8Bool.call   (c : ParserInputByteInU8.parse_with.closure) (tupled_args : Std.U8) :
  Result Bool :=
  EvalInputByteInBackendU8.eval.closure.Insts.CoreOpsFunctionFnTupleShared1U8Bool.call c tupled_args

abbrev ParserInputByteInU8.parse_with.closure.Insts.CoreOpsFunctionFnMutTupleShared1U8Bool.call_mut   (state : ParserInputByteInU8.parse_with.closure) (args : Std.U8) :
  Result (Bool × ParserInputByteInU8.parse_with.closure) :=
  EvalInputByteInBackendU8.eval.closure.Insts.CoreOpsFunctionFnMutTupleShared1U8Bool.call_mut state args

abbrev ParserInputByteInU8.parse_with.closure.Insts.CoreOpsFunctionFnOnceTupleShared1U8Bool.call_once   (c : ParserInputByteInU8.parse_with.closure) (i : Std.U8) : Result Bool :=
  EvalInputByteInBackendU8.eval.closure.Insts.CoreOpsFunctionFnOnceTupleShared1U8Bool.call_once c i

abbrev ParserInputByteInU8.parse_with.closure.Insts.CoreOpsFunctionFnOnceTupleShared1U8Bool   : core.ops.function.FnOnce ParserInputByteInU8.parse_with.closure Std.U8 Bool :=
  EvalInputByteInBackendU8.eval.closure.Insts.CoreOpsFunctionFnOnceTupleShared1U8Bool Direct

abbrev ParserInputByteInU8.parse_with.closure.Insts.CoreOpsFunctionFnMutTupleShared1U8Bool   : core.ops.function.FnMut ParserInputByteInU8.parse_with.closure Std.U8 Bool :=
  EvalInputByteInBackendU8.eval.closure.Insts.CoreOpsFunctionFnMutTupleShared1U8Bool Direct

abbrev ParserInputByteInU8.parse_with.closure.Insts.CoreOpsFunctionFnTupleShared1U8Bool   : core.ops.function.Fn ParserInputByteInU8.parse_with.closure Std.U8 Bool :=
  EvalInputByteInBackendU8.eval.closure.Insts.CoreOpsFunctionFnTupleShared1U8Bool Direct

abbrev ParserInputByteNotInU8.parse_with.closure  :=
  EvalInputByteNotInBackendU8.eval.closure Direct

abbrev ParserInputByteNotInU8.parse_with.closure.Insts.CoreOpsFunctionFnTupleShared1U8Bool.call   (c : ParserInputByteNotInU8.parse_with.closure) (tupled_args : Std.U8) :
  Result Bool :=
  EvalInputByteNotInBackendU8.eval.closure.Insts.CoreOpsFunctionFnTupleShared1U8Bool.call c tupled_args

abbrev ParserInputByteNotInU8.parse_with.closure.Insts.CoreOpsFunctionFnMutTupleShared1U8Bool.call_mut   (state : ParserInputByteNotInU8.parse_with.closure) (args : Std.U8) :
  Result (Bool × ParserInputByteNotInU8.parse_with.closure) :=
  EvalInputByteNotInBackendU8.eval.closure.Insts.CoreOpsFunctionFnMutTupleShared1U8Bool.call_mut state args

abbrev ParserInputByteNotInU8.parse_with.closure.Insts.CoreOpsFunctionFnOnceTupleShared1U8Bool.call_once   (c : ParserInputByteNotInU8.parse_with.closure) (i : Std.U8) :
  Result Bool :=
  EvalInputByteNotInBackendU8.eval.closure.Insts.CoreOpsFunctionFnOnceTupleShared1U8Bool.call_once c i

abbrev ParserInputByteNotInU8.parse_with.closure.Insts.CoreOpsFunctionFnOnceTupleShared1U8Bool   : core.ops.function.FnOnce ParserInputByteNotInU8.parse_with.closure Std.U8
  Bool :=
  EvalInputByteNotInBackendU8.eval.closure.Insts.CoreOpsFunctionFnOnceTupleShared1U8Bool Direct

abbrev ParserInputByteNotInU8.parse_with.closure.Insts.CoreOpsFunctionFnMutTupleShared1U8Bool   : core.ops.function.FnMut ParserInputByteNotInU8.parse_with.closure Std.U8
  Bool :=
  EvalInputByteNotInBackendU8.eval.closure.Insts.CoreOpsFunctionFnMutTupleShared1U8Bool Direct

abbrev ParserInputByteNotInU8.parse_with.closure.Insts.CoreOpsFunctionFnTupleShared1U8Bool   : core.ops.function.Fn ParserInputByteNotInU8.parse_with.closure Std.U8 Bool :=
  EvalInputByteNotInBackendU8.eval.closure.Insts.CoreOpsFunctionFnTupleShared1U8Bool Direct

abbrev ParserInputIntRangeT.parse_with.closure (P : Type) (T : Type) :=
  EvalInputIntRangeBackendT.eval.closure Direct P T

abbrev ParserInputIntRangeT.parse_with.closure.Insts.CoreOpsFunctionFnTupleShared1TBool.call   {P : Type} {T : Type} (ParserInst : DirectParser P T) (corecmpOrdInst :
  core.cmp.Ord T) (c : ParserInputIntRangeT.parse_with.closure P T)
  (tupled_args : T) :
  Result Bool :=
  EvalInputIntRangeBackendT.eval.closure.Insts.CoreOpsFunctionFnTupleShared1TBool.call ParserInst corecmpOrdInst c tupled_args

abbrev ParserInputIntRangeT.parse_with.closure.Insts.CoreOpsFunctionFnMutTupleShared1TBool.call_mut   {P : Type} {T : Type} (ParserInst : DirectParser P T) (corecmpOrdInst :
  core.cmp.Ord T) (state : ParserInputIntRangeT.parse_with.closure P T)
  (args : T) :
  Result (Bool × (ParserInputIntRangeT.parse_with.closure P T)) :=
  EvalInputIntRangeBackendT.eval.closure.Insts.CoreOpsFunctionFnMutTupleShared1TBool.call_mut ParserInst corecmpOrdInst state args

abbrev ParserInputIntRangeT.parse_with.closure.Insts.CoreOpsFunctionFnOnceTupleShared1TBool.call_once   {P : Type} {T : Type} (ParserInst : DirectParser P T) (corecmpOrdInst :
  core.cmp.Ord T) (c : ParserInputIntRangeT.parse_with.closure P T) (t : T) :
  Result Bool :=
  EvalInputIntRangeBackendT.eval.closure.Insts.CoreOpsFunctionFnOnceTupleShared1TBool.call_once ParserInst corecmpOrdInst c t

abbrev ParserInputIntRangeT.parse_with.closure.Insts.CoreOpsFunctionFnOnceTupleShared1TBool   {P : Type} {T : Type} (ParserInst : DirectParser P T) (corecmpOrdInst :
  core.cmp.Ord T) : core.ops.function.FnOnce
  (ParserInputIntRangeT.parse_with.closure P T) T Bool :=
  EvalInputIntRangeBackendT.eval.closure.Insts.CoreOpsFunctionFnOnceTupleShared1TBool ParserInst corecmpOrdInst

abbrev ParserInputIntRangeT.parse_with.closure.Insts.CoreOpsFunctionFnMutTupleShared1TBool   {P : Type} {T : Type} (ParserInst : DirectParser P T) (corecmpOrdInst :
  core.cmp.Ord T) : core.ops.function.FnMut
  (ParserInputIntRangeT.parse_with.closure P T) T Bool :=
  EvalInputIntRangeBackendT.eval.closure.Insts.CoreOpsFunctionFnMutTupleShared1TBool ParserInst corecmpOrdInst

abbrev ParserInputIntRangeT.parse_with.closure.Insts.CoreOpsFunctionFnTupleShared1TBool   {P : Type} {T : Type} (ParserInst : DirectParser P T) (corecmpOrdInst :
  core.cmp.Ord T) : core.ops.function.Fn
  (ParserInputIntRangeT.parse_with.closure P T) T Bool :=
  EvalInputIntRangeBackendT.eval.closure.Insts.CoreOpsFunctionFnTupleShared1TBool ParserInst corecmpOrdInst

attribute [direct_lift] eval_direct Std.bind_assoc bind_ok

@[direct_lift] theorem grammar.numeric.Bits.Insts.RusthammerParserInputU64.parse_with_lift (self : Bits) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Bits.Insts.RusthammerParser_traitsEvalInputBackendU64.eval self () input cursor context = (do
    let outcome ← Bits.Insts.RusthammerParserInputU64.parse_with self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (Bits.Insts.RusthammerParserInputU64 ) self input cursor context

@[direct_lift] theorem dependent_examples.CountPrefix.Insts.RusthammerParserInputUsize.parse_with_lift (self : dependent_examples.CountPrefix) (input : Slice Std.U8)
  (cursor : Cursor) (context : ParseContext) :
  dependent_examples.CountPrefix.Insts.RusthammerParser_traitsEvalInputBackendUsize.eval self () input cursor context = (do
    let outcome ← dependent_examples.CountPrefix.Insts.RusthammerParserInputUsize.parse_with self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (dependent_examples.CountPrefix.Insts.RusthammerParserInputUsize ) self input cursor context

@[direct_lift] theorem grammar.bytes.TakeAligned.Insts.RusthammerParserInputSharedInputSliceU8.parse_with_lift (self : TakeAligned) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  TakeAligned.Insts.RusthammerParser_traitsEvalInputBackendSharedSliceU8.eval self () input cursor context = (do
    let outcome ← TakeAligned.Insts.RusthammerParserInputSharedInputSliceU8.parse_with self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (TakeAligned.Insts.RusthammerParserInputSharedInputSliceU8 ) self input cursor context

@[direct_lift] theorem grammar.repeat.Repeat.Insts.RusthammerParserInputVec.parse_with_lift {P : Type} {Clause0_Output : Type} (ParserInst : DirectParser P Clause0_Output)
  (self : Repeat P) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Repeat.Insts.RusthammerParser_traitsEvalInputBackendVec.eval ParserInst self () input cursor context = (do
    let outcome ← Repeat.Insts.RusthammerParserInputVec.parse_with ParserInst self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (Repeat.Insts.RusthammerParserInputVec ParserInst) self input cursor context

@[direct_lift] theorem grammar.transform.Map.Insts.RusthammerParser.parse_with_lift {P : Type} {F : Type} {O : Type} {Clause0_Output : Type} (ParserInst : DirectParser
  P Clause0_Output) (coreopsfunctionFnFTupleClause0_OutputOInst :
  core.ops.function.Fn F Clause0_Output O) (self : Map P F)
  (input : Slice Std.U8) (cursor : Cursor) (context : ParseContext) :
  Map.Insts.RusthammerParser_traitsEval.eval ParserInst coreopsfunctionFnFTupleClause0_OutputOInst self () input cursor context = (do
    let outcome ← Map.Insts.RusthammerParser.parse_with ParserInst coreopsfunctionFnFTupleClause0_OutputOInst self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (Map.Insts.RusthammerParser ParserInst coreopsfunctionFnFTupleClause0_OutputOInst) self input cursor context

@[direct_lift] theorem grammar.sequence.Seq.Insts.RusthammerParserInputPair.parse_with_lift {P : Type} {Q : Type} {Clause0_Output : Type} {Clause1_Output : Type}
  (ParserInst : DirectParser P Clause0_Output) (ParserInst1 : DirectParser Q
  Clause1_Output) (self : Seq P Q) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Seq.Insts.RusthammerParser_traitsEvalInputBackendPair.eval ParserInst ParserInst1 self () input cursor context = (do
    let outcome ← Seq.Insts.RusthammerParserInputPair.parse_with ParserInst ParserInst1 self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (Seq.Insts.RusthammerParserInputPair ParserInst ParserInst1) self input cursor context

@[direct_lift] theorem grammar.numeric.Bit.Insts.RusthammerParserInputBool.parse_with_lift (self : Bit) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Bit.Insts.RusthammerParser_traitsEvalInputBackendBool.eval self () input cursor context = (do
    let outcome ← Bit.Insts.RusthammerParserInputBool.parse_with self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (Bit.Insts.RusthammerParserInputBool ) self input cursor context

@[direct_lift] theorem grammar.control.Choice.Insts.RusthammerParser.parse_with_lift {P : Type} {Q : Type} {Clause0_Output : Type} (ParserInst : DirectParser P
  Clause0_Output) (ParserInst1 : DirectParser Q Clause0_Output) (self : Choice P Q)
  (input : Slice Std.U8) (cursor : Cursor) (context : ParseContext) :
  Choice.Insts.RusthammerParser_traitsEval.eval ParserInst ParserInst1 self () input cursor context = (do
    let outcome ← Choice.Insts.RusthammerParser.parse_with ParserInst ParserInst1 self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (Choice.Insts.RusthammerParser ParserInst ParserInst1) self input cursor context

@[direct_lift] theorem grammar.position.End.Insts.RusthammerParserInputTuple.parse_with_lift (self : End) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  End.Insts.RusthammerParser_traitsEvalInputBackendTuple.eval self () input cursor context = (do
    let outcome ← End.Insts.RusthammerParserInputTuple.parse_with self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (End.Insts.RusthammerParserInputTuple ) self input cursor context

@[direct_lift] theorem grammar.numeric.Literal.Insts.RusthammerParserInputU64.parse_with_lift (self : Literal) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Literal.Insts.RusthammerParser_traitsEvalInputBackendU64.eval self () input cursor context = (do
    let outcome ← Literal.Insts.RusthammerParserInputU64.parse_with self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (Literal.Insts.RusthammerParserInputU64 ) self input cursor context

@[direct_lift] theorem marker_example.Marker.Insts.RusthammerParserInputU64.parse_with_lift (self : marker_example.Marker) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  marker_example.Marker.Insts.RusthammerParser_traitsEvalInputBackendU64.eval self () input cursor context = (do
    let outcome ← marker_example.Marker.Insts.RusthammerParserInputU64.parse_with self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (marker_example.Marker.Insts.RusthammerParserInputU64 ) self input cursor context

@[direct_lift] theorem record_example.RecordParser.Insts.RusthammerParserInputRecord.parse_with_lift (self : record_example.RecordParser) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  record_example.RecordParser.Insts.RusthammerParser_traitsEvalInputBackendRecord.eval self () input cursor context = (do
    let outcome ← record_example.RecordParser.Insts.RusthammerParserInputRecord.parse_with self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (record_example.RecordParser.Insts.RusthammerParserInputRecord ) self input cursor context

@[direct_lift] theorem grammar.position.SkipBits.Insts.RusthammerParserInputTuple.parse_with_lift (self : SkipBits) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  SkipBits.Insts.RusthammerParser_traitsEvalInputBackendTuple.eval self () input cursor context = (do
    let outcome ← SkipBits.Insts.RusthammerParserInputTuple.parse_with self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (SkipBits.Insts.RusthammerParserInputTuple ) self input cursor context

@[direct_lift] theorem grammar.position.Tell.Insts.RusthammerParserInputCursor.parse_with_lift (self : Tell) (input : Slice Std.U8) (cursor : Cursor)
  (_context : ParseContext) :
  Tell.Insts.RusthammerParser_traitsEvalInputBackendCursor.eval self () input cursor _context = (do
    let outcome ← Tell.Insts.RusthammerParserInputCursor.parse_with self input cursor _context
    ok (outcome, ())) := by
  exact eval_direct (Tell.Insts.RusthammerParserInputCursor ) self input cursor _context

@[direct_lift] theorem Shared0P.Insts.RusthammerParser.parse_with_lift {P : Type} {Clause0_Output : Type} (ParserInst : DirectParser P Clause0_Output)
  (self : P) (input : Slice Std.U8) (cursor : Cursor) (context : ParseContext) :
  Shared0P.Insts.RusthammerParser_traitsEval.eval ParserInst self () input cursor context = (do
    let outcome ← Shared0P.Insts.RusthammerParser.parse_with ParserInst self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (Shared0P.Insts.RusthammerParser ParserInst) self input cursor context

@[direct_lift] theorem grammar.order.WithOrder.Insts.RusthammerParser.parse_with_lift {P : Type} {Clause0_Output : Type} (ParserInst : DirectParser P Clause0_Output)
  (self : WithOrder P) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  WithOrder.Insts.RusthammerParser_traitsEval.eval ParserInst self () input cursor context = (do
    let outcome ← WithOrder.Insts.RusthammerParser.parse_with ParserInst self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (WithOrder.Insts.RusthammerParser ParserInst) self input cursor context

@[direct_lift] theorem grammar.numeric.SignedBits.Insts.RusthammerParserInputI64.parse_with_lift (self : SignedBits) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  SignedBits.Insts.RusthammerParser_traitsEvalInputBackendI64.eval self () input cursor context = (do
    let outcome ← SignedBits.Insts.RusthammerParserInputI64.parse_with self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (SignedBits.Insts.RusthammerParserInputI64 ) self input cursor context

@[direct_lift] theorem grammar.numeric.Byte.Insts.RusthammerParserInputU8.parse_with_lift (self : Code.grammar.numeric.Byte) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Code.grammar.numeric.Byte.Insts.RusthammerParser_traitsEvalInputBackendU8.eval self () input cursor context = (do
    let outcome ← Code.grammar.numeric.Byte.Insts.RusthammerParserInputU8.parse_with self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (Code.grammar.numeric.Byte.Insts.RusthammerParserInputU8 ) self input cursor context

@[direct_lift] theorem grammar.numeric.BeU16.Insts.RusthammerParserInputU16.parse_with_lift (self : BeU16) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  BeU16.Insts.RusthammerParser_traitsEvalInputBackendU16.eval self () input cursor context = (do
    let outcome ← BeU16.Insts.RusthammerParserInputU16.parse_with self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (BeU16.Insts.RusthammerParserInputU16 ) self input cursor context

@[direct_lift] theorem grammar.numeric.BeU32.Insts.RusthammerParserInputU32.parse_with_lift (self : BeU32) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  BeU32.Insts.RusthammerParser_traitsEvalInputBackendU32.eval self () input cursor context = (do
    let outcome ← BeU32.Insts.RusthammerParserInputU32.parse_with self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (BeU32.Insts.RusthammerParserInputU32 ) self input cursor context

@[direct_lift] theorem grammar.numeric.BeU64.Insts.RusthammerParserInputU64.parse_with_lift (self : BeU64) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  BeU64.Insts.RusthammerParser_traitsEvalInputBackendU64.eval self () input cursor context = (do
    let outcome ← BeU64.Insts.RusthammerParserInputU64.parse_with self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (BeU64.Insts.RusthammerParserInputU64 ) self input cursor context

@[direct_lift] theorem grammar.numeric.I8.Insts.RusthammerParserInputI8.parse_with_lift (self : Code.grammar.numeric.I8) (input : Slice Std.U8) (cursor : Cursor) (context : ParseContext) :
  Code.grammar.numeric.I8.Insts.RusthammerParser_traitsEvalInputBackendI8.eval self () input cursor context = (do
    let outcome ← Code.grammar.numeric.I8.Insts.RusthammerParserInputI8.parse_with self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (Code.grammar.numeric.I8.Insts.RusthammerParserInputI8 ) self input cursor context

@[direct_lift] theorem grammar.numeric.BeI16.Insts.RusthammerParserInputI16.parse_with_lift (self : BeI16) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  BeI16.Insts.RusthammerParser_traitsEvalInputBackendI16.eval self () input cursor context = (do
    let outcome ← BeI16.Insts.RusthammerParserInputI16.parse_with self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (BeI16.Insts.RusthammerParserInputI16 ) self input cursor context

@[direct_lift] theorem grammar.numeric.BeI32.Insts.RusthammerParserInputI32.parse_with_lift (self : BeI32) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  BeI32.Insts.RusthammerParser_traitsEvalInputBackendI32.eval self () input cursor context = (do
    let outcome ← BeI32.Insts.RusthammerParserInputI32.parse_with self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (BeI32.Insts.RusthammerParserInputI32 ) self input cursor context

@[direct_lift] theorem grammar.numeric.BeI64.Insts.RusthammerParserInputI64.parse_with_lift (self : BeI64) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  BeI64.Insts.RusthammerParser_traitsEvalInputBackendI64.eval self () input cursor context = (do
    let outcome ← BeI64.Insts.RusthammerParserInputI64.parse_with self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (BeI64.Insts.RusthammerParserInputI64 ) self input cursor context

@[direct_lift] theorem grammar.bytes.ByteIn.Insts.RusthammerParserInputU8.parse_with_lift (self : ByteIn) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  ByteIn.Insts.RusthammerParser_traitsEvalInputBackendU8.eval self () input cursor context = (do
    let outcome ← ByteIn.Insts.RusthammerParserInputU8.parse_with self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (ByteIn.Insts.RusthammerParserInputU8 ) self input cursor context

@[direct_lift] theorem grammar.bytes.ByteNotIn.Insts.RusthammerParserInputU8.parse_with_lift (self : ByteNotIn) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  ByteNotIn.Insts.RusthammerParser_traitsEvalInputBackendU8.eval self () input cursor context = (do
    let outcome ← ByteNotIn.Insts.RusthammerParserInputU8.parse_with self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (ByteNotIn.Insts.RusthammerParserInputU8 ) self input cursor context

@[direct_lift] theorem grammar.bytes.BytePattern.Insts.RusthammerParserInputSharedPatternSliceU8.parse_with_lift (self : BytePattern) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  BytePattern.Insts.RusthammerParser_traitsEvalInputBackendSharedSliceU8.eval self () input cursor context = (do
    let outcome ← BytePattern.Insts.RusthammerParserInputSharedPatternSliceU8.parse_with self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (BytePattern.Insts.RusthammerParserInputSharedPatternSliceU8 ) self input cursor context

@[direct_lift] theorem grammar.control.Epsilon.Insts.RusthammerParserInputTuple.parse_with_lift (self : Epsilon) (s : Slice Std.U8) (cursor : Cursor) (pc : ParseContext) :
  Epsilon.Insts.RusthammerParser_traitsEvalInputBackendTuple.eval self () s cursor pc = (do
    let outcome ← Epsilon.Insts.RusthammerParserInputTuple.parse_with self s cursor pc
    ok (outcome, ())) := by
  exact eval_direct (Epsilon.Insts.RusthammerParserInputTuple ) self s cursor pc

@[direct_lift] theorem grammar.control.Fail.Insts.RusthammerParser.parse_with_lift {T : Type} (self : Fail T) (s : Slice Std.U8) (c : Cursor)
  (pc : ParseContext) :
  Fail.Insts.RusthammerParser_traitsEval.eval self () s c pc = (do
    let outcome ← Fail.Insts.RusthammerParser.parse_with self s c pc
    ok (outcome, ())) := by
  exact eval_direct (Fail.Insts.RusthammerParser T) self s c pc

@[direct_lift] theorem grammar.sequence.Bind.Insts.RusthammerParser.parse_with_lift {P : Type} {F : Type} {Q : Type} {Clause0_Output : Type} {Clause2_Output :
  Type} (ParserInst : DirectParser P Clause0_Output)
  (coreopsfunctionFnFTupleClause0_OutputQInst : core.ops.function.Fn F
  Clause0_Output Q) (ParserInst1 : DirectParser Q Clause2_Output) (self : Bind P F)
  (input : Slice Std.U8) (cursor : Cursor) (context : ParseContext) :
  Bind.Insts.RusthammerParser_traitsEval.eval ParserInst coreopsfunctionFnFTupleClause0_OutputQInst ParserInst1 self () input cursor context = (do
    let outcome ← Bind.Insts.RusthammerParser.parse_with ParserInst coreopsfunctionFnFTupleClause0_OutputQInst ParserInst1 self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (Bind.Insts.RusthammerParser ParserInst coreopsfunctionFnFTupleClause0_OutputQInst ParserInst1) self input cursor context

@[direct_lift] theorem grammar.sequence.Left.Insts.RusthammerParser.parse_with_lift {P : Type} {Q : Type} {Clause0_Output : Type} {Clause1_Output : Type}
  (ParserInst : DirectParser P Clause0_Output) (ParserInst1 : DirectParser Q
  Clause1_Output) (self : Left P Q) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Left.Insts.RusthammerParser_traitsEval.eval ParserInst ParserInst1 self () input cursor context = (do
    let outcome ← Left.Insts.RusthammerParser.parse_with ParserInst ParserInst1 self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (Left.Insts.RusthammerParser ParserInst ParserInst1) self input cursor context

@[direct_lift] theorem grammar.sequence.Right.Insts.RusthammerParser.parse_with_lift {P : Type} {Q : Type} {Clause0_Output : Type} {Clause1_Output : Type}
  (ParserInst : DirectParser P Clause0_Output) (ParserInst1 : DirectParser Q
  Clause1_Output) (self : Right P Q) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Right.Insts.RusthammerParser_traitsEval.eval ParserInst ParserInst1 self () input cursor context = (do
    let outcome ← Right.Insts.RusthammerParser.parse_with ParserInst ParserInst1 self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (Right.Insts.RusthammerParser ParserInst ParserInst1) self input cursor context

@[direct_lift] theorem grammar.sequence.Middle.Insts.RusthammerParser.parse_with_lift {L : Type} {P : Type} {R : Type} {Clause0_Output : Type} {Clause1_Output :
  Type} {Clause2_Output : Type} (ParserInst : DirectParser L Clause0_Output)
  (ParserInst1 : DirectParser P Clause1_Output) (ParserInst2 : DirectParser R
  Clause2_Output) (self : Middle L P R) (input : Slice Std.U8)
  (cursor : Cursor) (context : ParseContext) :
  Middle.Insts.RusthammerParser_traitsEval.eval ParserInst ParserInst1 ParserInst2 self () input cursor context = (do
    let outcome ← Middle.Insts.RusthammerParser.parse_with ParserInst ParserInst1 ParserInst2 self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (Middle.Insts.RusthammerParser ParserInst ParserInst1 ParserInst2) self input cursor context

@[direct_lift] theorem grammar.sequence.Ignore.Insts.RusthammerParserInputTuple.parse_with_lift {P : Type} {Clause0_Output : Type} (ParserInst : DirectParser P Clause0_Output)
  (self : Ignore P) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Ignore.Insts.RusthammerParser_traitsEvalInputBackendTuple.eval ParserInst self () input cursor context = (do
    let outcome ← Ignore.Insts.RusthammerParserInputTuple.parse_with ParserInst self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (Ignore.Insts.RusthammerParserInputTuple ParserInst) self input cursor context

@[direct_lift] theorem grammar.repeat.FoldRepeat.Insts.RusthammerParser.parse_with_lift {P : Type} {I : Type} {F : Type} {R : Type} {Clause0_Output : Type}
  (ParserInst : DirectParser P Clause0_Output) (coreopsfunctionFnITupleRInst :
  core.ops.function.Fn I Unit R) (coreopsfunctionFnFPairRInst :
  core.ops.function.Fn F (R × Clause0_Output) R) (self : FoldRepeat P I F)
  (input : Slice Std.U8) (cursor : Cursor) (context : ParseContext) :
  FoldRepeat.Insts.RusthammerParser_traitsEval.eval ParserInst coreopsfunctionFnITupleRInst coreopsfunctionFnFPairRInst self () input cursor context = (do
    let outcome ← FoldRepeat.Insts.RusthammerParser.parse_with ParserInst coreopsfunctionFnITupleRInst coreopsfunctionFnFPairRInst self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (FoldRepeat.Insts.RusthammerParser ParserInst coreopsfunctionFnITupleRInst coreopsfunctionFnFPairRInst) self input cursor context

@[direct_lift] theorem grammar.repeat.SepBy.Insts.RusthammerParserInputVec.parse_with_lift {P : Type} {S : Type} {Clause0_Output : Type} {Clause1_Output : Type}
  (ParserInst : DirectParser P Clause0_Output) (ParserInst1 : DirectParser S
  Clause1_Output) (self : SepBy P S) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  SepBy.Insts.RusthammerParser_traitsEvalInputBackendVec.eval ParserInst ParserInst1 self () input cursor context = (do
    let outcome ← SepBy.Insts.RusthammerParserInputVec.parse_with ParserInst ParserInst1 self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (SepBy.Insts.RusthammerParserInputVec ParserInst ParserInst1) self input cursor context

@[direct_lift] theorem grammar.repeat.FoldSepBy.Insts.RusthammerParser.parse_with_lift {P : Type} {S : Type} {I : Type} {F : Type} {R : Type} {Clause0_Output :
  Type} {Clause1_Output : Type} (ParserInst : DirectParser P Clause0_Output)
  (ParserInst1 : DirectParser S Clause1_Output) (coreopsfunctionFnITupleRInst :
  core.ops.function.Fn I Unit R) (coreopsfunctionFnFPairRInst :
  core.ops.function.Fn F (R × Clause0_Output) R) (self : FoldSepBy P S I F)
  (input : Slice Std.U8) (cursor : Cursor) (context : ParseContext) :
  FoldSepBy.Insts.RusthammerParser_traitsEval.eval ParserInst ParserInst1 coreopsfunctionFnITupleRInst coreopsfunctionFnFPairRInst self () input cursor context = (do
    let outcome ← FoldSepBy.Insts.RusthammerParser.parse_with ParserInst ParserInst1 coreopsfunctionFnITupleRInst coreopsfunctionFnFPairRInst self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (FoldSepBy.Insts.RusthammerParser ParserInst ParserInst1 coreopsfunctionFnITupleRInst coreopsfunctionFnFPairRInst) self input cursor context

@[direct_lift] theorem grammar.transform.TryMap.Insts.RusthammerParser.parse_with_lift {P : Type} {F : Type} {O : Type} {E : Type} {Clause0_Output : Type}
  (ParserInst : DirectParser P Clause0_Output)
  (coreopsfunctionFnFTupleClause0_OutputResultInst : core.ops.function.Fn F
  Clause0_Output (core.result.Result O E)) (self : TryMap P F)
  (input : Slice Std.U8) (cursor : Cursor) (context : ParseContext) :
  TryMap.Insts.RusthammerParser_traitsEval.eval ParserInst coreopsfunctionFnFTupleClause0_OutputResultInst self () input cursor context = (do
    let outcome ← TryMap.Insts.RusthammerParser.parse_with ParserInst coreopsfunctionFnFTupleClause0_OutputResultInst self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (TryMap.Insts.RusthammerParser ParserInst coreopsfunctionFnFTupleClause0_OutputResultInst) self input cursor context

@[direct_lift] theorem grammar.transform.Verify.Insts.RusthammerParser.parse_with_lift {P : Type} {F : Type} {Clause0_Output : Type} (ParserInst : DirectParser P
  Clause0_Output) (coreopsfunctionFnFTupleSharedInputClause0_OutputBoolInst :
  core.ops.function.Fn F Clause0_Output Bool) (self : Verify P F)
  (input : Slice Std.U8) (cursor : Cursor) (context : ParseContext) :
  Verify.Insts.RusthammerParser_traitsEval.eval ParserInst coreopsfunctionFnFTupleSharedInputClause0_OutputBoolInst self () input cursor context = (do
    let outcome ← Verify.Insts.RusthammerParser.parse_with ParserInst coreopsfunctionFnFTupleSharedInputClause0_OutputBoolInst self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (Verify.Insts.RusthammerParser ParserInst coreopsfunctionFnFTupleSharedInputClause0_OutputBoolInst) self input cursor context

@[direct_lift] theorem grammar.transform.IntRange.Insts.RusthammerParser.parse_with_lift {P : Type} {T : Type} (ParserInst : DirectParser P T) (corecmpOrdInst :
  core.cmp.Ord T) (self : IntRange P T) (input : Slice Std.U8)
  (cursor : Cursor) (context : ParseContext) :
  IntRange.Insts.RusthammerParser_traitsEval.eval ParserInst corecmpOrdInst self () input cursor context = (do
    let outcome ← IntRange.Insts.RusthammerParser.parse_with ParserInst corecmpOrdInst self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (IntRange.Insts.RusthammerParser ParserInst corecmpOrdInst) self input cursor context

@[direct_lift] theorem grammar.control.ButNot.Insts.RusthammerParser.parse_with_lift {P : Type} {Q : Type} {Clause0_Output : Type} {Clause1_Output : Type}
  (ParserInst : DirectParser P Clause0_Output) (ParserInst1 : DirectParser Q
  Clause1_Output) (self : ButNot P Q) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  ButNot.Insts.RusthammerParser_traitsEval.eval ParserInst ParserInst1 self () input cursor context = (do
    let outcome ← ButNot.Insts.RusthammerParser.parse_with ParserInst ParserInst1 self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (ButNot.Insts.RusthammerParser ParserInst ParserInst1) self input cursor context

@[direct_lift] theorem grammar.control.Difference.Insts.RusthammerParser.parse_with_lift {P : Type} {Q : Type} {Clause0_Output : Type} {Clause1_Output : Type}
  (ParserInst : DirectParser P Clause0_Output) (ParserInst1 : DirectParser Q
  Clause1_Output) (self : Difference P Q) (input : Slice Std.U8)
  (cursor : Cursor) (context : ParseContext) :
  Difference.Insts.RusthammerParser_traitsEval.eval ParserInst ParserInst1 self () input cursor context = (do
    let outcome ← Difference.Insts.RusthammerParser.parse_with ParserInst ParserInst1 self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (Difference.Insts.RusthammerParser ParserInst ParserInst1) self input cursor context

@[direct_lift] theorem grammar.control.Xor.Insts.RusthammerParser.parse_with_lift {P : Type} {Q : Type} {Clause0_Output : Type} (ParserInst : DirectParser P
  Clause0_Output) (ParserInst1 : DirectParser Q Clause0_Output) (self : Xor P Q)
  (input : Slice Std.U8) (cursor : Cursor) (context : ParseContext) :
  Xor.Insts.RusthammerParser_traitsEval.eval ParserInst ParserInst1 self () input cursor context = (do
    let outcome ← Xor.Insts.RusthammerParser.parse_with ParserInst ParserInst1 self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (Xor.Insts.RusthammerParser ParserInst ParserInst1) self input cursor context

@[direct_lift] theorem grammar.control.Optional.Insts.RusthammerParserInputOption.parse_with_lift {P : Type} {Clause0_Output : Type} (ParserInst : DirectParser P Clause0_Output)
  (self : Optional P) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Optional.Insts.RusthammerParser_traitsEvalInputBackendOption.eval ParserInst self () input cursor context = (do
    let outcome ← Optional.Insts.RusthammerParserInputOption.parse_with ParserInst self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (Optional.Insts.RusthammerParserInputOption ParserInst) self input cursor context

@[direct_lift] theorem grammar.control.And.Insts.RusthammerParserInputTuple.parse_with_lift {P : Type} {Clause0_Output : Type} (ParserInst : DirectParser P Clause0_Output)
  (self : And P) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  And.Insts.RusthammerParser_traitsEvalInputBackendTuple.eval ParserInst self () input cursor context = (do
    let outcome ← And.Insts.RusthammerParserInputTuple.parse_with ParserInst self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (And.Insts.RusthammerParserInputTuple ParserInst) self input cursor context

@[direct_lift] theorem grammar.control.Not.Insts.RusthammerParserInputTuple.parse_with_lift {P : Type} {Clause0_Output : Type} (ParserInst : DirectParser P Clause0_Output)
  (self : Not P) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Not.Insts.RusthammerParser_traitsEvalInputBackendTuple.eval ParserInst self () input cursor context = (do
    let outcome ← Not.Insts.RusthammerParserInputTuple.parse_with ParserInst self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (Not.Insts.RusthammerParserInputTuple ParserInst) self input cursor context

@[direct_lift] theorem DirectRun.repeat_parse_lift {P : Type} {Q : Type} {Clause0_Output : Type} (ParserInst : DirectParser P
  Clause0_Output) (ParserInst1 : DirectParser Q Clause0_Output) (parser : P)
  (following : Q) (count : Std.Usize) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  RustHammer.Code.grammar.repeat.repeat_parse ParserInst ParserInst1 () parser following count input cursor context = (do
    let outcome ← DirectRun.repeat_parse ParserInst ParserInst1 parser following count input cursor context
    ok (outcome, ())) := by
  unfold DirectRun.repeat_parse
  rw [Std.bind_assoc]
  conv_lhs => rw [← Std.bind_pure (RustHammer.Code.grammar.repeat.repeat_parse ParserInst ParserInst1 () parser following count input cursor context)]
  apply congrArg (Std.bind _)
  funext ⟨outcome, state⟩
  cases state
  simp [bind_ok]

@[direct_lift] theorem DirectRun.repeat_run_lift {P : Type} {A : Type} {Clause0_Output : Type} {Clause1_Output : Type}
  (ParserInst : DirectParser P Clause0_Output) (RepeatAccumulatorInst :
  RepeatAccumulator A Clause0_Output Clause1_Output) (parser : P)
  (bounds : RepeatBounds) (accumulator : A) (input : Slice Std.U8)
  (cursor : Cursor) (context : ParseContext) :
  RustHammer.Code.grammar.repeat.repeat_run ParserInst RepeatAccumulatorInst () parser bounds accumulator input cursor context = (do
    let outcome ← DirectRun.repeat_run ParserInst RepeatAccumulatorInst parser bounds accumulator input cursor context
    ok (outcome, ())) := by
  unfold DirectRun.repeat_run
  rw [Std.bind_assoc]
  conv_lhs => rw [← Std.bind_pure (RustHammer.Code.grammar.repeat.repeat_run ParserInst RepeatAccumulatorInst () parser bounds accumulator input cursor context)]
  apply congrArg (Std.bind _)
  funext ⟨outcome, state⟩
  cases state
  simp [bind_ok]

@[direct_lift] theorem DirectRun.repeat_run_with_lift {P : Type} {Q : Type} {A : Type} {Clause0_Output : Type} {Clause2_Output :
  Type} (ParserInst : DirectParser P Clause0_Output) (ParserInst1 : DirectParser Q
  Clause0_Output) (RepeatAccumulatorInst : RepeatAccumulator A Clause0_Output
  Clause2_Output) (parser : P) (following : Q) (bounds : RepeatBounds)
  (accumulator : A) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  RustHammer.Code.grammar.repeat.repeat_run_with ParserInst ParserInst1 RepeatAccumulatorInst () parser following bounds accumulator input cursor context = (do
    let outcome ← DirectRun.repeat_run_with ParserInst ParserInst1 RepeatAccumulatorInst parser following bounds accumulator input cursor context
    ok (outcome, ())) := by
  unfold DirectRun.repeat_run_with
  rw [Std.bind_assoc]
  conv_lhs => rw [← Std.bind_pure (RustHammer.Code.grammar.repeat.repeat_run_with ParserInst ParserInst1 RepeatAccumulatorInst () parser following bounds accumulator input cursor context)]
  apply congrArg (Std.bind _)
  funext ⟨outcome, state⟩
  cases state
  simp [bind_ok]

@[direct_lift] theorem DirectRun.restrict_match_lift {P : Type} {Q : Type} {Clause0_Output : Type} {Clause1_Output : Type}
  (ParserInst : DirectParser P Clause0_Output) (ParserInst1 : DirectParser Q
  Clause1_Output) (first : P) (second : Q) (input : Slice Std.U8)
  (cursor : Cursor) (context : ParseContext) (allow_equal : Bool) :
  RustHammer.Code.grammar.control.restrict_match ParserInst ParserInst1 () first second input cursor context allow_equal = (do
    let outcome ← DirectRun.restrict_match ParserInst ParserInst1 first second input cursor context allow_equal
    ok (outcome, ())) := by
  unfold DirectRun.restrict_match
  rw [Std.bind_assoc]
  conv_lhs => rw [← Std.bind_pure (RustHammer.Code.grammar.control.restrict_match ParserInst ParserInst1 () first second input cursor context allow_equal)]
  apply congrArg (Std.bind _)
  funext ⟨outcome, state⟩
  cases state
  simp [bind_ok]

@[direct_lift] theorem DirectRun.record_example.parse_record_body_lift (input : Slice Std.U8) (cursor : Cursor) (version : Std.U64)
  (flags : Std.U64) (count : Std.Usize) (context : ParseContext) :
  RustHammer.Code.record_example.parse_record_body () input cursor version flags count context = (do
    let outcome ← DirectRun.record_example.parse_record_body input cursor version flags count context
    ok (outcome, ())) := by
  unfold DirectRun.record_example.parse_record_body
  rw [Std.bind_assoc]
  conv_lhs => rw [← Std.bind_pure (RustHammer.Code.record_example.parse_record_body () input cursor version flags count context)]
  apply congrArg (Std.bind _)
  funext ⟨outcome, state⟩
  cases state
  simp [bind_ok]

@[direct_lift] theorem DirectRun.match_byte_pattern_lift (pattern : Slice Std.U8) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  RustHammer.Code.grammar.bytes.match_byte_pattern () pattern input cursor context = (do
    let outcome ← DirectRun.match_byte_pattern pattern input cursor context
    ok (outcome, ())) := by
  unfold DirectRun.match_byte_pattern
  rw [Std.bind_assoc]
  conv_lhs => rw [← Std.bind_pure (RustHammer.Code.grammar.bytes.match_byte_pattern () pattern input cursor context)]
  apply congrArg (Std.bind _)
  funext ⟨outcome, state⟩
  cases state
  simp [bind_ok]

@[direct_lift] theorem DirectRun.repeat_run_with_loop_lift {P : Type} {Q : Type} {A : Type} {Clause0_Output : Type} {Clause2_Output :
  Type} (ParserInst : DirectParser P Clause0_Output) (ParserInst1 : DirectParser Q
  Clause0_Output) (RepeatAccumulatorInst : RepeatAccumulator A Clause0_Output
  Clause2_Output) (parser : P) (following : Q) (i : Std.Usize)
  (o : Option Std.Usize) (accumulator : A) (input : Slice Std.U8)
  (context : ParseContext) (unbounded : Bool) (values : Clause2_Output)
  (next : Cursor) (count : Std.Usize) :
  RustHammer.Code.grammar.repeat.repeat_run_with_loop ParserInst ParserInst1 RepeatAccumulatorInst () parser following i o accumulator input context unbounded values next count = (do
    let outcome ← DirectRun.repeat_run_with_loop ParserInst ParserInst1 RepeatAccumulatorInst parser following i o accumulator input context unbounded values next count
    ok (outcome, ())) := by
  unfold DirectRun.repeat_run_with_loop
  rw [Std.bind_assoc]
  conv_lhs => rw [← Std.bind_pure (RustHammer.Code.grammar.repeat.repeat_run_with_loop ParserInst ParserInst1 RepeatAccumulatorInst () parser following i o accumulator input context unbounded values next count)]
  apply congrArg (Std.bind _)
  funext ⟨outcome, state⟩
  cases state
  simp [bind_ok]

@[direct_lift] theorem DirectRun.match_byte_pattern_loop_lift (pattern : Slice Std.U8) (input : Slice Std.U8) (context : ParseContext)
  (next : Cursor) (index : Std.Usize) :
  RustHammer.Code.grammar.bytes.match_byte_pattern_loop () pattern input context next index = (do
    let outcome ← DirectRun.match_byte_pattern_loop pattern input context next index
    ok (outcome, ())) := by
  unfold DirectRun.match_byte_pattern_loop
  rw [Std.bind_assoc]
  conv_lhs => rw [← Std.bind_pure (RustHammer.Code.grammar.bytes.match_byte_pattern_loop () pattern input context next index)]
  apply congrArg (Std.bind _)
  funext ⟨outcome, state⟩
  cases state
  simp [bind_ok]

end RustHammer.Code
