import RustHammer.DirectState

/-! Proof-facing names for direct execution of the extracted evaluators.
Each parser definition delegates to `DirectParser.parse_with`; the helper
definitions project the empty backend state in the same way. Retaining these
names keeps grammar contracts readable independently of Aeneas's state-passing
representation. The lift lemmas are proved equalities, not assumed models.

Keep the projection functions as `def`: making them reducible would let the
inverse `direct_lift` rewrites repeatedly expose and rewrite their own bodies. -/

open Aeneas Aeneas.Std Result
namespace RustHammer.Code

abbrev Bits.Insts.RusthammerParserInputU64 : DirectParser Bits Std.U64 :=
  Bits.Insts.RusthammerEvalInputBackendU64 Direct

def Bits.Insts.RusthammerParserInputU64.parse_with (self : Bits) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome Std.U64) :=
  DirectParser.parse_with (Bits.Insts.RusthammerParserInputU64 ) self input cursor context

abbrev dependent_examples.CountPrefix.Insts.RusthammerParserInputUsize :
  DirectParser dependent_examples.CountPrefix Std.Usize :=
  dependent_examples.CountPrefix.Insts.RusthammerEvalInputBackendUsize Direct

def dependent_examples.CountPrefix.Insts.RusthammerParserInputUsize.parse_with (self : dependent_examples.CountPrefix) (input : Slice Std.U8)
  (cursor : Cursor) (context : ParseContext) :
  Result (ParseOutcome Std.Usize) :=
  DirectParser.parse_with (dependent_examples.CountPrefix.Insts.RusthammerParserInputUsize ) self input cursor context

abbrev TakeAligned.Insts.RusthammerParserInputSharedInputSliceU8 : DirectParser
  TakeAligned (Slice Std.U8) :=
  TakeAligned.Insts.RusthammerEvalInputBackendSharedSliceU8 Direct

def TakeAligned.Insts.RusthammerParserInputSharedInputSliceU8.parse_with (self : TakeAligned) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome (Slice Std.U8)) :=
  DirectParser.parse_with (TakeAligned.Insts.RusthammerParserInputSharedInputSliceU8 ) self input cursor context

abbrev Repeat.Insts.RusthammerParserInputVec {P : Type} {Clause0_Output :
  Type} (ParserInst : DirectParser P Clause0_Output) : DirectParser (Repeat P)
  (alloc.vec.Vec Clause0_Output) :=
  Repeat.Insts.RusthammerEvalInputBackendVec ParserInst

def Repeat.Insts.RusthammerParserInputVec.parse_with {P : Type} {Clause0_Output : Type} (ParserInst : DirectParser P Clause0_Output)
  (self : Repeat P) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome (alloc.vec.Vec Clause0_Output)) :=
  DirectParser.parse_with (Repeat.Insts.RusthammerParserInputVec ParserInst) self input cursor context

abbrev Map.Insts.RusthammerParser {P : Type} {F : Type} {O : Type}
  {Clause0_Output : Type} (ParserInst : DirectParser P Clause0_Output)
  (coreopsfunctionFnFTupleClause0_OutputOInst : core.ops.function.Fn F
  Clause0_Output O) : DirectParser (Map P F) O :=
  Map.Insts.RusthammerEval ParserInst coreopsfunctionFnFTupleClause0_OutputOInst

def Map.Insts.RusthammerParser.parse_with {P : Type} {F : Type} {O : Type} {Clause0_Output : Type} (ParserInst : DirectParser
  P Clause0_Output) (coreopsfunctionFnFTupleClause0_OutputOInst :
  core.ops.function.Fn F Clause0_Output O) (self : Map P F)
  (input : Slice Std.U8) (cursor : Cursor) (context : ParseContext) :
  Result (ParseOutcome O) :=
  DirectParser.parse_with (Map.Insts.RusthammerParser ParserInst coreopsfunctionFnFTupleClause0_OutputOInst) self input cursor context

abbrev Seq.Insts.RusthammerParserInputPair {P : Type} {Q : Type}
  {Clause0_Output : Type} {Clause1_Output : Type} (ParserInst : DirectParser P
  Clause0_Output) (ParserInst1 : DirectParser Q Clause1_Output) : DirectParser (Seq P Q)
  (Clause0_Output × Clause1_Output) :=
  Seq.Insts.RusthammerEvalInputBackendPair ParserInst ParserInst1

def Seq.Insts.RusthammerParserInputPair.parse_with {P : Type} {Q : Type} {Clause0_Output : Type} {Clause1_Output : Type}
  (ParserInst : DirectParser P Clause0_Output) (ParserInst1 : DirectParser Q
  Clause1_Output) (self : Seq P Q) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome (Clause0_Output × Clause1_Output)) :=
  DirectParser.parse_with (Seq.Insts.RusthammerParserInputPair ParserInst ParserInst1) self input cursor context

abbrev Bit.Insts.RusthammerParserInputBool : DirectParser Bit Bool :=
  Bit.Insts.RusthammerEvalInputBackendBool Direct

def Bit.Insts.RusthammerParserInputBool.parse_with (self : Bit) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome Bool) :=
  DirectParser.parse_with (Bit.Insts.RusthammerParserInputBool ) self input cursor context

abbrev Choice.Insts.RusthammerParser {P : Type} {Q : Type} {Clause0_Output :
  Type} (ParserInst : DirectParser P Clause0_Output) (ParserInst1 : DirectParser Q
  Clause0_Output) : DirectParser (Choice P Q) Clause0_Output :=
  Choice.Insts.RusthammerEval ParserInst ParserInst1

def Choice.Insts.RusthammerParser.parse_with {P : Type} {Q : Type} {Clause0_Output : Type} (ParserInst : DirectParser P
  Clause0_Output) (ParserInst1 : DirectParser Q Clause0_Output) (self : Choice P Q)
  (input : Slice Std.U8) (cursor : Cursor) (context : ParseContext) :
  Result (ParseOutcome Clause0_Output) :=
  DirectParser.parse_with (Choice.Insts.RusthammerParser ParserInst ParserInst1) self input cursor context

abbrev End.Insts.RusthammerParserInputTuple : DirectParser End Unit :=
  End.Insts.RusthammerEvalInputBackendTuple Direct

def End.Insts.RusthammerParserInputTuple.parse_with (self : End) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome Unit) :=
  DirectParser.parse_with (End.Insts.RusthammerParserInputTuple ) self input cursor context

abbrev Literal.Insts.RusthammerParserInputU64 : DirectParser Literal Std.U64 :=
  Literal.Insts.RusthammerEvalInputBackendU64 Direct

def Literal.Insts.RusthammerParserInputU64.parse_with (self : Literal) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome Std.U64) :=
  DirectParser.parse_with (Literal.Insts.RusthammerParserInputU64 ) self input cursor context

abbrev marker_example.Marker.Insts.RusthammerParserInputU64 : DirectParser
  marker_example.Marker Std.U64 :=
  marker_example.Marker.Insts.RusthammerEvalInputBackendU64 Direct

def marker_example.Marker.Insts.RusthammerParserInputU64.parse_with (self : marker_example.Marker) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome Std.U64) :=
  DirectParser.parse_with (marker_example.Marker.Insts.RusthammerParserInputU64 ) self input cursor context

abbrev record_example.RecordParser.Insts.RusthammerParserInputRecord : DirectParser
  record_example.RecordParser record_example.Record :=
  record_example.RecordParser.Insts.RusthammerEvalInputBackendRecord Direct

def record_example.RecordParser.Insts.RusthammerParserInputRecord.parse_with (self : record_example.RecordParser) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome record_example.Record) :=
  DirectParser.parse_with (record_example.RecordParser.Insts.RusthammerParserInputRecord ) self input cursor context

abbrev SkipBits.Insts.RusthammerParserInputTuple : DirectParser SkipBits Unit :=
  SkipBits.Insts.RusthammerEvalInputBackendTuple Direct

def SkipBits.Insts.RusthammerParserInputTuple.parse_with (self : SkipBits) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome Unit) :=
  DirectParser.parse_with (SkipBits.Insts.RusthammerParserInputTuple ) self input cursor context

abbrev Tell.Insts.RusthammerParserInputCursor : DirectParser Tell Cursor :=
  Tell.Insts.RusthammerEvalInputBackendCursor Direct

def Tell.Insts.RusthammerParserInputCursor.parse_with (self : Tell) (input : Slice Std.U8) (cursor : Cursor)
  (_context : ParseContext) :
  Result (ParseOutcome Cursor) :=
  DirectParser.parse_with (Tell.Insts.RusthammerParserInputCursor ) self input cursor _context

abbrev Shared0P.Insts.RusthammerParser {P : Type} {Clause0_Output : Type}
  (ParserInst : DirectParser P Clause0_Output) : DirectParser P Clause0_Output :=
  Shared0P.Insts.RusthammerEval ParserInst

def Shared0P.Insts.RusthammerParser.parse_with {P : Type} {Clause0_Output : Type} (ParserInst : DirectParser P Clause0_Output)
  (self : P) (input : Slice Std.U8) (cursor : Cursor) (context : ParseContext)
  :
  Result (ParseOutcome Clause0_Output) :=
  DirectParser.parse_with (Shared0P.Insts.RusthammerParser ParserInst) self input cursor context

def Shared0P.Insts.RusthammerParser.parse   {P : Type} {Clause0_Output : Type} (ParserInst : DirectParser P Clause0_Output)
  (self : P) (input : Slice Std.U8) (cursor : Cursor) :
  Result (core.result.Result (Cursor × Clause0_Output) ParseError) :=
  DirectParser.parse (Shared0P.Insts.RusthammerParser ParserInst) self input cursor

abbrev WithOrder.Insts.RusthammerParser {P : Type} {Clause0_Output : Type}
  (ParserInst : DirectParser P Clause0_Output) : DirectParser (WithOrder P) Clause0_Output :=
  WithOrder.Insts.RusthammerEval ParserInst

def WithOrder.Insts.RusthammerParser.parse_with {P : Type} {Clause0_Output : Type} (ParserInst : DirectParser P Clause0_Output)
  (self : WithOrder P) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome Clause0_Output) :=
  DirectParser.parse_with (WithOrder.Insts.RusthammerParser ParserInst) self input cursor context

abbrev SignedBits.Insts.RusthammerParserInputI64 : DirectParser SignedBits Std.I64 :=
  SignedBits.Insts.RusthammerEvalInputBackendI64 Direct

def SignedBits.Insts.RusthammerParserInputI64.parse_with (self : SignedBits) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome Std.I64) :=
  DirectParser.parse_with (SignedBits.Insts.RusthammerParserInputI64 ) self input cursor context

abbrev Byte.Insts.RusthammerParserInputU8 : DirectParser Byte Std.U8 :=
  Byte.Insts.RusthammerEvalInputBackendU8 Direct

def Byte.Insts.RusthammerParserInputU8.parse_with (self : Byte) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome Std.U8) :=
  DirectParser.parse_with (Byte.Insts.RusthammerParserInputU8 ) self input cursor context

abbrev BeU16.Insts.RusthammerParserInputU16 : DirectParser BeU16 Std.U16 :=
  BeU16.Insts.RusthammerEvalInputBackendU16 Direct

def BeU16.Insts.RusthammerParserInputU16.parse_with (self : BeU16) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome Std.U16) :=
  DirectParser.parse_with (BeU16.Insts.RusthammerParserInputU16 ) self input cursor context

abbrev BeU32.Insts.RusthammerParserInputU32 : DirectParser BeU32 Std.U32 :=
  BeU32.Insts.RusthammerEvalInputBackendU32 Direct

def BeU32.Insts.RusthammerParserInputU32.parse_with (self : BeU32) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome Std.U32) :=
  DirectParser.parse_with (BeU32.Insts.RusthammerParserInputU32 ) self input cursor context

abbrev BeU64.Insts.RusthammerParserInputU64 : DirectParser BeU64 Std.U64 :=
  BeU64.Insts.RusthammerEvalInputBackendU64 Direct

def BeU64.Insts.RusthammerParserInputU64.parse_with (self : BeU64) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome Std.U64) :=
  DirectParser.parse_with (BeU64.Insts.RusthammerParserInputU64 ) self input cursor context

abbrev I8.Insts.RusthammerParserInputI8 : DirectParser I8 Std.I8 :=
  I8.Insts.RusthammerEvalInputBackendI8 Direct

def I8.Insts.RusthammerParserInputI8.parse_with (self : I8) (input : Slice Std.U8) (cursor : Cursor) (context : ParseContext)
  :
  Result (ParseOutcome Std.I8) :=
  DirectParser.parse_with (I8.Insts.RusthammerParserInputI8 ) self input cursor context

abbrev BeI16.Insts.RusthammerParserInputI16 : DirectParser BeI16 Std.I16 :=
  BeI16.Insts.RusthammerEvalInputBackendI16 Direct

def BeI16.Insts.RusthammerParserInputI16.parse_with (self : BeI16) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome Std.I16) :=
  DirectParser.parse_with (BeI16.Insts.RusthammerParserInputI16 ) self input cursor context

abbrev BeI32.Insts.RusthammerParserInputI32 : DirectParser BeI32 Std.I32 :=
  BeI32.Insts.RusthammerEvalInputBackendI32 Direct

def BeI32.Insts.RusthammerParserInputI32.parse_with (self : BeI32) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome Std.I32) :=
  DirectParser.parse_with (BeI32.Insts.RusthammerParserInputI32 ) self input cursor context

abbrev BeI64.Insts.RusthammerParserInputI64 : DirectParser BeI64 Std.I64 :=
  BeI64.Insts.RusthammerEvalInputBackendI64 Direct

def BeI64.Insts.RusthammerParserInputI64.parse_with (self : BeI64) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome Std.I64) :=
  DirectParser.parse_with (BeI64.Insts.RusthammerParserInputI64 ) self input cursor context

abbrev ByteIn.Insts.RusthammerParserInputU8 : DirectParser ByteIn Std.U8 :=
  ByteIn.Insts.RusthammerEvalInputBackendU8 Direct

def ByteIn.Insts.RusthammerParserInputU8.parse_with (self : ByteIn) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome Std.U8) :=
  DirectParser.parse_with (ByteIn.Insts.RusthammerParserInputU8 ) self input cursor context

abbrev ByteNotIn.Insts.RusthammerParserInputU8 : DirectParser ByteNotIn Std.U8 :=
  ByteNotIn.Insts.RusthammerEvalInputBackendU8 Direct

def ByteNotIn.Insts.RusthammerParserInputU8.parse_with (self : ByteNotIn) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome Std.U8) :=
  DirectParser.parse_with (ByteNotIn.Insts.RusthammerParserInputU8 ) self input cursor context

abbrev BytePattern.Insts.RusthammerParserInputSharedPatternSliceU8 : DirectParser
  BytePattern (Slice Std.U8) :=
  BytePattern.Insts.RusthammerEvalInputBackendSharedSliceU8 Direct

def BytePattern.Insts.RusthammerParserInputSharedPatternSliceU8.parse_with (self : BytePattern) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome (Slice Std.U8)) :=
  DirectParser.parse_with (BytePattern.Insts.RusthammerParserInputSharedPatternSliceU8 ) self input cursor context

abbrev Epsilon.Insts.RusthammerParserInputTuple : DirectParser Epsilon Unit :=
  Epsilon.Insts.RusthammerEvalInputBackendTuple Direct

def Epsilon.Insts.RusthammerParserInputTuple.parse_with (self : Epsilon) (s : Slice Std.U8) (cursor : Cursor) (pc : ParseContext) :
  Result (ParseOutcome Unit) :=
  DirectParser.parse_with (Epsilon.Insts.RusthammerParserInputTuple ) self s cursor pc

abbrev Fail.Insts.RusthammerParser (T : Type) : DirectParser (Fail T) T :=
  Fail.Insts.RusthammerEval Direct T

def Fail.Insts.RusthammerParser.parse_with {T : Type} (self : Fail T) (s : Slice Std.U8) (c : Cursor)
  (pc : ParseContext) :
  Result (ParseOutcome T) :=
  DirectParser.parse_with (Fail.Insts.RusthammerParser T) self s c pc

abbrev Bind.Insts.RusthammerParser {P : Type} {F : Type} {Q : Type}
  {Clause0_Output : Type} {Clause2_Output : Type} (ParserInst : DirectParser P
  Clause0_Output) (coreopsfunctionFnFTupleClause0_OutputQInst :
  core.ops.function.Fn F Clause0_Output Q) (ParserInst1 : DirectParser Q
  Clause2_Output) : DirectParser (Bind P F) Clause2_Output :=
  Bind.Insts.RusthammerEval ParserInst coreopsfunctionFnFTupleClause0_OutputQInst ParserInst1

def Bind.Insts.RusthammerParser.parse_with {P : Type} {F : Type} {Q : Type} {Clause0_Output : Type} {Clause2_Output :
  Type} (ParserInst : DirectParser P Clause0_Output)
  (coreopsfunctionFnFTupleClause0_OutputQInst : core.ops.function.Fn F
  Clause0_Output Q) (ParserInst1 : DirectParser Q Clause2_Output) (self : Bind P F)
  (input : Slice Std.U8) (cursor : Cursor) (context : ParseContext) :
  Result (ParseOutcome Clause2_Output) :=
  DirectParser.parse_with (Bind.Insts.RusthammerParser ParserInst coreopsfunctionFnFTupleClause0_OutputQInst ParserInst1) self input cursor context

abbrev Left.Insts.RusthammerParser {P : Type} {Q : Type} {Clause0_Output :
  Type} {Clause1_Output : Type} (ParserInst : DirectParser P Clause0_Output)
  (ParserInst1 : DirectParser Q Clause1_Output) : DirectParser (Left P Q) Clause0_Output :=
  Left.Insts.RusthammerEval ParserInst ParserInst1

def Left.Insts.RusthammerParser.parse_with {P : Type} {Q : Type} {Clause0_Output : Type} {Clause1_Output : Type}
  (ParserInst : DirectParser P Clause0_Output) (ParserInst1 : DirectParser Q
  Clause1_Output) (self : Left P Q) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome Clause0_Output) :=
  DirectParser.parse_with (Left.Insts.RusthammerParser ParserInst ParserInst1) self input cursor context

abbrev Right.Insts.RusthammerParser {P : Type} {Q : Type} {Clause0_Output :
  Type} {Clause1_Output : Type} (ParserInst : DirectParser P Clause0_Output)
  (ParserInst1 : DirectParser Q Clause1_Output) : DirectParser (Right P Q) Clause1_Output :=
  Right.Insts.RusthammerEval ParserInst ParserInst1

def Right.Insts.RusthammerParser.parse_with {P : Type} {Q : Type} {Clause0_Output : Type} {Clause1_Output : Type}
  (ParserInst : DirectParser P Clause0_Output) (ParserInst1 : DirectParser Q
  Clause1_Output) (self : Right P Q) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome Clause1_Output) :=
  DirectParser.parse_with (Right.Insts.RusthammerParser ParserInst ParserInst1) self input cursor context

abbrev Middle.Insts.RusthammerParser {L : Type} {P : Type} {R : Type}
  {Clause0_Output : Type} {Clause1_Output : Type} {Clause2_Output : Type}
  (ParserInst : DirectParser L Clause0_Output) (ParserInst1 : DirectParser P
  Clause1_Output) (ParserInst2 : DirectParser R Clause2_Output) : DirectParser (Middle L P
  R) Clause1_Output :=
  Middle.Insts.RusthammerEval ParserInst ParserInst1 ParserInst2

def Middle.Insts.RusthammerParser.parse_with {L : Type} {P : Type} {R : Type} {Clause0_Output : Type} {Clause1_Output :
  Type} {Clause2_Output : Type} (ParserInst : DirectParser L Clause0_Output)
  (ParserInst1 : DirectParser P Clause1_Output) (ParserInst2 : DirectParser R
  Clause2_Output) (self : Middle L P R) (input : Slice Std.U8)
  (cursor : Cursor) (context : ParseContext) :
  Result (ParseOutcome Clause1_Output) :=
  DirectParser.parse_with (Middle.Insts.RusthammerParser ParserInst ParserInst1 ParserInst2) self input cursor context

abbrev Ignore.Insts.RusthammerParserInputTuple {P : Type} {Clause0_Output :
  Type} (ParserInst : DirectParser P Clause0_Output) : DirectParser (Ignore P) Unit :=
  Ignore.Insts.RusthammerEvalInputBackendTuple ParserInst

def Ignore.Insts.RusthammerParserInputTuple.parse_with {P : Type} {Clause0_Output : Type} (ParserInst : DirectParser P Clause0_Output)
  (self : Ignore P) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome Unit) :=
  DirectParser.parse_with (Ignore.Insts.RusthammerParserInputTuple ParserInst) self input cursor context

abbrev FoldRepeat.Insts.RusthammerParser {P : Type} {I : Type} {F : Type} {R
  : Type} {Clause0_Output : Type} (ParserInst : DirectParser P Clause0_Output)
  (coreopsfunctionFnITupleRInst : core.ops.function.Fn I Unit R)
  (coreopsfunctionFnFPairRInst : core.ops.function.Fn F (R × Clause0_Output)
  R) : DirectParser (FoldRepeat P I F) R :=
  FoldRepeat.Insts.RusthammerEval ParserInst coreopsfunctionFnITupleRInst coreopsfunctionFnFPairRInst

def FoldRepeat.Insts.RusthammerParser.parse_with {P : Type} {I : Type} {F : Type} {R : Type} {Clause0_Output : Type}
  (ParserInst : DirectParser P Clause0_Output) (coreopsfunctionFnITupleRInst :
  core.ops.function.Fn I Unit R) (coreopsfunctionFnFPairRInst :
  core.ops.function.Fn F (R × Clause0_Output) R) (self : FoldRepeat P I F)
  (input : Slice Std.U8) (cursor : Cursor) (context : ParseContext) :
  Result (ParseOutcome R) :=
  DirectParser.parse_with (FoldRepeat.Insts.RusthammerParser ParserInst coreopsfunctionFnITupleRInst coreopsfunctionFnFPairRInst) self input cursor context

abbrev SepBy.Insts.RusthammerParserInputVec {P : Type} {S : Type}
  {Clause0_Output : Type} {Clause1_Output : Type} (ParserInst : DirectParser P
  Clause0_Output) (ParserInst1 : DirectParser S Clause1_Output) : DirectParser (SepBy P S)
  (alloc.vec.Vec Clause0_Output) :=
  SepBy.Insts.RusthammerEvalInputBackendVec ParserInst ParserInst1

def SepBy.Insts.RusthammerParserInputVec.parse_with {P : Type} {S : Type} {Clause0_Output : Type} {Clause1_Output : Type}
  (ParserInst : DirectParser P Clause0_Output) (ParserInst1 : DirectParser S
  Clause1_Output) (self : SepBy P S) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome (alloc.vec.Vec Clause0_Output)) :=
  DirectParser.parse_with (SepBy.Insts.RusthammerParserInputVec ParserInst ParserInst1) self input cursor context

abbrev FoldSepBy.Insts.RusthammerParser {P : Type} {S : Type} {I : Type} {F :
  Type} {R : Type} {Clause0_Output : Type} {Clause1_Output : Type} (ParserInst
  : DirectParser P Clause0_Output) (ParserInst1 : DirectParser S Clause1_Output)
  (coreopsfunctionFnITupleRInst : core.ops.function.Fn I Unit R)
  (coreopsfunctionFnFPairRInst : core.ops.function.Fn F (R × Clause0_Output)
  R) : DirectParser (FoldSepBy P S I F) R :=
  FoldSepBy.Insts.RusthammerEval ParserInst ParserInst1 coreopsfunctionFnITupleRInst coreopsfunctionFnFPairRInst

def FoldSepBy.Insts.RusthammerParser.parse_with {P : Type} {S : Type} {I : Type} {F : Type} {R : Type} {Clause0_Output :
  Type} {Clause1_Output : Type} (ParserInst : DirectParser P Clause0_Output)
  (ParserInst1 : DirectParser S Clause1_Output) (coreopsfunctionFnITupleRInst :
  core.ops.function.Fn I Unit R) (coreopsfunctionFnFPairRInst :
  core.ops.function.Fn F (R × Clause0_Output) R) (self : FoldSepBy P S I F)
  (input : Slice Std.U8) (cursor : Cursor) (context : ParseContext) :
  Result (ParseOutcome R) :=
  DirectParser.parse_with (FoldSepBy.Insts.RusthammerParser ParserInst ParserInst1 coreopsfunctionFnITupleRInst coreopsfunctionFnFPairRInst) self input cursor context

abbrev TryMap.Insts.RusthammerParser {P : Type} {F : Type} {O : Type} {E :
  Type} {Clause0_Output : Type} (ParserInst : DirectParser P Clause0_Output)
  (coreopsfunctionFnFTupleClause0_OutputResultInst : core.ops.function.Fn F
  Clause0_Output (core.result.Result O E)) : DirectParser (TryMap P F) O :=
  TryMap.Insts.RusthammerEval ParserInst coreopsfunctionFnFTupleClause0_OutputResultInst

def TryMap.Insts.RusthammerParser.parse_with {P : Type} {F : Type} {O : Type} {E : Type} {Clause0_Output : Type}
  (ParserInst : DirectParser P Clause0_Output)
  (coreopsfunctionFnFTupleClause0_OutputResultInst : core.ops.function.Fn F
  Clause0_Output (core.result.Result O E)) (self : TryMap P F)
  (input : Slice Std.U8) (cursor : Cursor) (context : ParseContext) :
  Result (ParseOutcome O) :=
  DirectParser.parse_with (TryMap.Insts.RusthammerParser ParserInst coreopsfunctionFnFTupleClause0_OutputResultInst) self input cursor context

abbrev Verify.Insts.RusthammerParser {P : Type} {F : Type} {Clause0_Output :
  Type} (ParserInst : DirectParser P Clause0_Output)
  (coreopsfunctionFnFTupleSharedInputClause0_OutputBoolInst :
  core.ops.function.Fn F Clause0_Output Bool) : DirectParser (Verify P F)
  Clause0_Output :=
  Verify.Insts.RusthammerEval ParserInst coreopsfunctionFnFTupleSharedInputClause0_OutputBoolInst

def Verify.Insts.RusthammerParser.parse_with {P : Type} {F : Type} {Clause0_Output : Type} (ParserInst : DirectParser P
  Clause0_Output) (coreopsfunctionFnFTupleSharedInputClause0_OutputBoolInst :
  core.ops.function.Fn F Clause0_Output Bool) (self : Verify P F)
  (input : Slice Std.U8) (cursor : Cursor) (context : ParseContext) :
  Result (ParseOutcome Clause0_Output) :=
  DirectParser.parse_with (Verify.Insts.RusthammerParser ParserInst coreopsfunctionFnFTupleSharedInputClause0_OutputBoolInst) self input cursor context

abbrev IntRange.Insts.RusthammerParser {P : Type} {T : Type} (ParserInst :
  DirectParser P T) (corecmpOrdInst : core.cmp.Ord T) : DirectParser (IntRange P T) T :=
  IntRange.Insts.RusthammerEval ParserInst corecmpOrdInst

def IntRange.Insts.RusthammerParser.parse_with {P : Type} {T : Type} (ParserInst : DirectParser P T) (corecmpOrdInst :
  core.cmp.Ord T) (self : IntRange P T) (input : Slice Std.U8)
  (cursor : Cursor) (context : ParseContext) :
  Result (ParseOutcome T) :=
  DirectParser.parse_with (IntRange.Insts.RusthammerParser ParserInst corecmpOrdInst) self input cursor context

abbrev ButNot.Insts.RusthammerParser {P : Type} {Q : Type} {Clause0_Output :
  Type} {Clause1_Output : Type} (ParserInst : DirectParser P Clause0_Output)
  (ParserInst1 : DirectParser Q Clause1_Output) : DirectParser (ButNot P Q) Clause0_Output :=
  ButNot.Insts.RusthammerEval ParserInst ParserInst1

def ButNot.Insts.RusthammerParser.parse_with {P : Type} {Q : Type} {Clause0_Output : Type} {Clause1_Output : Type}
  (ParserInst : DirectParser P Clause0_Output) (ParserInst1 : DirectParser Q
  Clause1_Output) (self : ButNot P Q) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome Clause0_Output) :=
  DirectParser.parse_with (ButNot.Insts.RusthammerParser ParserInst ParserInst1) self input cursor context

abbrev Difference.Insts.RusthammerParser {P : Type} {Q : Type}
  {Clause0_Output : Type} {Clause1_Output : Type} (ParserInst : DirectParser P
  Clause0_Output) (ParserInst1 : DirectParser Q Clause1_Output) : DirectParser (Difference
  P Q) Clause0_Output :=
  Difference.Insts.RusthammerEval ParserInst ParserInst1

def Difference.Insts.RusthammerParser.parse_with {P : Type} {Q : Type} {Clause0_Output : Type} {Clause1_Output : Type}
  (ParserInst : DirectParser P Clause0_Output) (ParserInst1 : DirectParser Q
  Clause1_Output) (self : Difference P Q) (input : Slice Std.U8)
  (cursor : Cursor) (context : ParseContext) :
  Result (ParseOutcome Clause0_Output) :=
  DirectParser.parse_with (Difference.Insts.RusthammerParser ParserInst ParserInst1) self input cursor context

abbrev Xor.Insts.RusthammerParser {P : Type} {Q : Type} {Clause0_Output :
  Type} (ParserInst : DirectParser P Clause0_Output) (ParserInst1 : DirectParser Q
  Clause0_Output) : DirectParser (Xor P Q) Clause0_Output :=
  Xor.Insts.RusthammerEval ParserInst ParserInst1

def Xor.Insts.RusthammerParser.parse_with {P : Type} {Q : Type} {Clause0_Output : Type} (ParserInst : DirectParser P
  Clause0_Output) (ParserInst1 : DirectParser Q Clause0_Output) (self : Xor P Q)
  (input : Slice Std.U8) (cursor : Cursor) (context : ParseContext) :
  Result (ParseOutcome Clause0_Output) :=
  DirectParser.parse_with (Xor.Insts.RusthammerParser ParserInst ParserInst1) self input cursor context

abbrev Optional.Insts.RusthammerParserInputOption {P : Type} {Clause0_Output
  : Type} (ParserInst : DirectParser P Clause0_Output) : DirectParser (Optional P) (Option
  Clause0_Output) :=
  Optional.Insts.RusthammerEvalInputBackendOption ParserInst

def Optional.Insts.RusthammerParserInputOption.parse_with {P : Type} {Clause0_Output : Type} (ParserInst : DirectParser P Clause0_Output)
  (self : Optional P) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome (Option Clause0_Output)) :=
  DirectParser.parse_with (Optional.Insts.RusthammerParserInputOption ParserInst) self input cursor context

abbrev And.Insts.RusthammerParserInputTuple {P : Type} {Clause0_Output :
  Type} (ParserInst : DirectParser P Clause0_Output) : DirectParser (And P) Unit :=
  And.Insts.RusthammerEvalInputBackendTuple ParserInst

def And.Insts.RusthammerParserInputTuple.parse_with {P : Type} {Clause0_Output : Type} (ParserInst : DirectParser P Clause0_Output)
  (self : And P) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome Unit) :=
  DirectParser.parse_with (And.Insts.RusthammerParserInputTuple ParserInst) self input cursor context

abbrev Not.Insts.RusthammerParserInputTuple {P : Type} {Clause0_Output :
  Type} (ParserInst : DirectParser P Clause0_Output) : DirectParser (Not P) Unit :=
  Not.Insts.RusthammerEvalInputBackendTuple ParserInst

def Not.Insts.RusthammerParserInputTuple.parse_with {P : Type} {Clause0_Output : Type} (ParserInst : DirectParser P Clause0_Output)
  (self : Not P) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome Unit) :=
  DirectParser.parse_with (Not.Insts.RusthammerParserInputTuple ParserInst) self input cursor context

def DirectRun.repeat_parse   {P : Type} {Q : Type} {Clause0_Output : Type} (ParserInst : DirectParser P
  Clause0_Output) (ParserInst1 : DirectParser Q Clause0_Output) (parser : P)
  (following : Q) (count : Std.Usize) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome Clause0_Output) := do
  let (outcome, _) ← RustHammer.Code.repeat_parse ParserInst ParserInst1 () parser following count input cursor context
  ok outcome

def DirectRun.repeat_run   {P : Type} {A : Type} {Clause0_Output : Type} {Clause1_Output : Type}
  (ParserInst : DirectParser P Clause0_Output) (RepeatAccumulatorInst :
  RepeatAccumulator A Clause0_Output Clause1_Output) (parser : P)
  (bounds : RepeatBounds) (accumulator : A) (input : Slice Std.U8)
  (cursor : Cursor) (context : ParseContext) :
  Result (ParseOutcome Clause1_Output) := do
  let (outcome, _) ← RustHammer.Code.repeat_run ParserInst RepeatAccumulatorInst () parser bounds accumulator input cursor context
  ok outcome

def DirectRun.repeat_run_with   {P : Type} {Q : Type} {A : Type} {Clause0_Output : Type} {Clause2_Output :
  Type} (ParserInst : DirectParser P Clause0_Output) (ParserInst1 : DirectParser Q
  Clause0_Output) (RepeatAccumulatorInst : RepeatAccumulator A Clause0_Output
  Clause2_Output) (parser : P) (following : Q) (bounds : RepeatBounds)
  (accumulator : A) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome Clause2_Output) := do
  let (outcome, _) ← RustHammer.Code.repeat_run_with ParserInst ParserInst1 RepeatAccumulatorInst () parser following bounds accumulator input cursor context
  ok outcome

def DirectRun.restrict_match   {P : Type} {Q : Type} {Clause0_Output : Type} {Clause1_Output : Type}
  (ParserInst : DirectParser P Clause0_Output) (ParserInst1 : DirectParser Q
  Clause1_Output) (first : P) (second : Q) (input : Slice Std.U8)
  (cursor : Cursor) (context : ParseContext) (allow_equal : Bool) :
  Result (ParseOutcome Clause0_Output) := do
  let (outcome, _) ← RustHammer.Code.restrict_match ParserInst ParserInst1 () first second input cursor context allow_equal
  ok outcome

def DirectRun.record_example.parse_record_body   (input : Slice Std.U8) (cursor : Cursor) (version : Std.U64)
  (flags : Std.U64) (count : Std.Usize) (context : ParseContext) :
  Result (ParseOutcome record_example.Record) := do
  let (outcome, _) ← RustHammer.Code.record_example.parse_record_body () input cursor version flags count context
  ok outcome

def DirectRun.match_byte_pattern   (pattern : Slice Std.U8) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Result (ParseOutcome Unit) := do
  let (outcome, _) ← RustHammer.Code.match_byte_pattern () pattern input cursor context
  ok outcome

def DirectRun.repeat_run_with_loop   {P : Type} {Q : Type} {A : Type} {Clause0_Output : Type} {Clause2_Output :
  Type} (ParserInst : DirectParser P Clause0_Output) (ParserInst1 : DirectParser Q
  Clause0_Output) (RepeatAccumulatorInst : RepeatAccumulator A Clause0_Output
  Clause2_Output) (parser : P) (following : Q) (i : Std.Usize)
  (o : Option Std.Usize) (accumulator : A) (input : Slice Std.U8)
  (context : ParseContext) (unbounded : Bool) (values : Clause2_Output)
  (next : Cursor) (count : Std.Usize) :
  Result (ParseOutcome Clause2_Output) := do
  let (outcome, _) ← RustHammer.Code.repeat_run_with_loop ParserInst ParserInst1 RepeatAccumulatorInst () parser following i o accumulator input context unbounded values next count
  ok outcome

def DirectRun.match_byte_pattern_loop   (pattern : Slice Std.U8) (input : Slice Std.U8) (context : ParseContext)
  (next : Cursor) (index : Std.Usize) :
  Result (ParseOutcome Unit) := do
  let (outcome, _) ← RustHammer.Code.match_byte_pattern_loop () pattern input context next index
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

@[direct_lift] theorem Bits.Insts.RusthammerParserInputU64.parse_with_lift (self : Bits) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Bits.Insts.RusthammerEvalInputBackendU64.eval self () input cursor context = (do
    let outcome ← Bits.Insts.RusthammerParserInputU64.parse_with self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (Bits.Insts.RusthammerParserInputU64 ) self input cursor context

@[direct_lift] theorem dependent_examples.CountPrefix.Insts.RusthammerParserInputUsize.parse_with_lift (self : dependent_examples.CountPrefix) (input : Slice Std.U8)
  (cursor : Cursor) (context : ParseContext) :
  dependent_examples.CountPrefix.Insts.RusthammerEvalInputBackendUsize.eval self () input cursor context = (do
    let outcome ← dependent_examples.CountPrefix.Insts.RusthammerParserInputUsize.parse_with self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (dependent_examples.CountPrefix.Insts.RusthammerParserInputUsize ) self input cursor context

@[direct_lift] theorem TakeAligned.Insts.RusthammerParserInputSharedInputSliceU8.parse_with_lift (self : TakeAligned) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  TakeAligned.Insts.RusthammerEvalInputBackendSharedSliceU8.eval self () input cursor context = (do
    let outcome ← TakeAligned.Insts.RusthammerParserInputSharedInputSliceU8.parse_with self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (TakeAligned.Insts.RusthammerParserInputSharedInputSliceU8 ) self input cursor context

@[direct_lift] theorem Repeat.Insts.RusthammerParserInputVec.parse_with_lift {P : Type} {Clause0_Output : Type} (ParserInst : DirectParser P Clause0_Output)
  (self : Repeat P) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Repeat.Insts.RusthammerEvalInputBackendVec.eval ParserInst self () input cursor context = (do
    let outcome ← Repeat.Insts.RusthammerParserInputVec.parse_with ParserInst self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (Repeat.Insts.RusthammerParserInputVec ParserInst) self input cursor context

@[direct_lift] theorem Map.Insts.RusthammerParser.parse_with_lift {P : Type} {F : Type} {O : Type} {Clause0_Output : Type} (ParserInst : DirectParser
  P Clause0_Output) (coreopsfunctionFnFTupleClause0_OutputOInst :
  core.ops.function.Fn F Clause0_Output O) (self : Map P F)
  (input : Slice Std.U8) (cursor : Cursor) (context : ParseContext) :
  Map.Insts.RusthammerEval.eval ParserInst coreopsfunctionFnFTupleClause0_OutputOInst self () input cursor context = (do
    let outcome ← Map.Insts.RusthammerParser.parse_with ParserInst coreopsfunctionFnFTupleClause0_OutputOInst self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (Map.Insts.RusthammerParser ParserInst coreopsfunctionFnFTupleClause0_OutputOInst) self input cursor context

@[direct_lift] theorem Seq.Insts.RusthammerParserInputPair.parse_with_lift {P : Type} {Q : Type} {Clause0_Output : Type} {Clause1_Output : Type}
  (ParserInst : DirectParser P Clause0_Output) (ParserInst1 : DirectParser Q
  Clause1_Output) (self : Seq P Q) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Seq.Insts.RusthammerEvalInputBackendPair.eval ParserInst ParserInst1 self () input cursor context = (do
    let outcome ← Seq.Insts.RusthammerParserInputPair.parse_with ParserInst ParserInst1 self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (Seq.Insts.RusthammerParserInputPair ParserInst ParserInst1) self input cursor context

@[direct_lift] theorem Bit.Insts.RusthammerParserInputBool.parse_with_lift (self : Bit) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Bit.Insts.RusthammerEvalInputBackendBool.eval self () input cursor context = (do
    let outcome ← Bit.Insts.RusthammerParserInputBool.parse_with self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (Bit.Insts.RusthammerParserInputBool ) self input cursor context

@[direct_lift] theorem Choice.Insts.RusthammerParser.parse_with_lift {P : Type} {Q : Type} {Clause0_Output : Type} (ParserInst : DirectParser P
  Clause0_Output) (ParserInst1 : DirectParser Q Clause0_Output) (self : Choice P Q)
  (input : Slice Std.U8) (cursor : Cursor) (context : ParseContext) :
  Choice.Insts.RusthammerEval.eval ParserInst ParserInst1 self () input cursor context = (do
    let outcome ← Choice.Insts.RusthammerParser.parse_with ParserInst ParserInst1 self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (Choice.Insts.RusthammerParser ParserInst ParserInst1) self input cursor context

@[direct_lift] theorem End.Insts.RusthammerParserInputTuple.parse_with_lift (self : End) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  End.Insts.RusthammerEvalInputBackendTuple.eval self () input cursor context = (do
    let outcome ← End.Insts.RusthammerParserInputTuple.parse_with self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (End.Insts.RusthammerParserInputTuple ) self input cursor context

@[direct_lift] theorem Literal.Insts.RusthammerParserInputU64.parse_with_lift (self : Literal) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Literal.Insts.RusthammerEvalInputBackendU64.eval self () input cursor context = (do
    let outcome ← Literal.Insts.RusthammerParserInputU64.parse_with self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (Literal.Insts.RusthammerParserInputU64 ) self input cursor context

@[direct_lift] theorem marker_example.Marker.Insts.RusthammerParserInputU64.parse_with_lift (self : marker_example.Marker) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  marker_example.Marker.Insts.RusthammerEvalInputBackendU64.eval self () input cursor context = (do
    let outcome ← marker_example.Marker.Insts.RusthammerParserInputU64.parse_with self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (marker_example.Marker.Insts.RusthammerParserInputU64 ) self input cursor context

@[direct_lift] theorem record_example.RecordParser.Insts.RusthammerParserInputRecord.parse_with_lift (self : record_example.RecordParser) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  record_example.RecordParser.Insts.RusthammerEvalInputBackendRecord.eval self () input cursor context = (do
    let outcome ← record_example.RecordParser.Insts.RusthammerParserInputRecord.parse_with self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (record_example.RecordParser.Insts.RusthammerParserInputRecord ) self input cursor context

@[direct_lift] theorem SkipBits.Insts.RusthammerParserInputTuple.parse_with_lift (self : SkipBits) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  SkipBits.Insts.RusthammerEvalInputBackendTuple.eval self () input cursor context = (do
    let outcome ← SkipBits.Insts.RusthammerParserInputTuple.parse_with self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (SkipBits.Insts.RusthammerParserInputTuple ) self input cursor context

@[direct_lift] theorem Tell.Insts.RusthammerParserInputCursor.parse_with_lift (self : Tell) (input : Slice Std.U8) (cursor : Cursor)
  (_context : ParseContext) :
  Tell.Insts.RusthammerEvalInputBackendCursor.eval self () input cursor _context = (do
    let outcome ← Tell.Insts.RusthammerParserInputCursor.parse_with self input cursor _context
    ok (outcome, ())) := by
  exact eval_direct (Tell.Insts.RusthammerParserInputCursor ) self input cursor _context

@[direct_lift] theorem Shared0P.Insts.RusthammerParser.parse_with_lift {P : Type} {Clause0_Output : Type} (ParserInst : DirectParser P Clause0_Output)
  (self : P) (input : Slice Std.U8) (cursor : Cursor) (context : ParseContext) :
  Shared0P.Insts.RusthammerEval.eval ParserInst self () input cursor context = (do
    let outcome ← Shared0P.Insts.RusthammerParser.parse_with ParserInst self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (Shared0P.Insts.RusthammerParser ParserInst) self input cursor context

@[direct_lift] theorem WithOrder.Insts.RusthammerParser.parse_with_lift {P : Type} {Clause0_Output : Type} (ParserInst : DirectParser P Clause0_Output)
  (self : WithOrder P) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  WithOrder.Insts.RusthammerEval.eval ParserInst self () input cursor context = (do
    let outcome ← WithOrder.Insts.RusthammerParser.parse_with ParserInst self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (WithOrder.Insts.RusthammerParser ParserInst) self input cursor context

@[direct_lift] theorem SignedBits.Insts.RusthammerParserInputI64.parse_with_lift (self : SignedBits) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  SignedBits.Insts.RusthammerEvalInputBackendI64.eval self () input cursor context = (do
    let outcome ← SignedBits.Insts.RusthammerParserInputI64.parse_with self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (SignedBits.Insts.RusthammerParserInputI64 ) self input cursor context

@[direct_lift] theorem Byte.Insts.RusthammerParserInputU8.parse_with_lift (self : Byte) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Byte.Insts.RusthammerEvalInputBackendU8.eval self () input cursor context = (do
    let outcome ← Byte.Insts.RusthammerParserInputU8.parse_with self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (Byte.Insts.RusthammerParserInputU8 ) self input cursor context

@[direct_lift] theorem BeU16.Insts.RusthammerParserInputU16.parse_with_lift (self : BeU16) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  BeU16.Insts.RusthammerEvalInputBackendU16.eval self () input cursor context = (do
    let outcome ← BeU16.Insts.RusthammerParserInputU16.parse_with self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (BeU16.Insts.RusthammerParserInputU16 ) self input cursor context

@[direct_lift] theorem BeU32.Insts.RusthammerParserInputU32.parse_with_lift (self : BeU32) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  BeU32.Insts.RusthammerEvalInputBackendU32.eval self () input cursor context = (do
    let outcome ← BeU32.Insts.RusthammerParserInputU32.parse_with self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (BeU32.Insts.RusthammerParserInputU32 ) self input cursor context

@[direct_lift] theorem BeU64.Insts.RusthammerParserInputU64.parse_with_lift (self : BeU64) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  BeU64.Insts.RusthammerEvalInputBackendU64.eval self () input cursor context = (do
    let outcome ← BeU64.Insts.RusthammerParserInputU64.parse_with self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (BeU64.Insts.RusthammerParserInputU64 ) self input cursor context

@[direct_lift] theorem I8.Insts.RusthammerParserInputI8.parse_with_lift (self : I8) (input : Slice Std.U8) (cursor : Cursor) (context : ParseContext) :
  I8.Insts.RusthammerEvalInputBackendI8.eval self () input cursor context = (do
    let outcome ← I8.Insts.RusthammerParserInputI8.parse_with self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (I8.Insts.RusthammerParserInputI8 ) self input cursor context

@[direct_lift] theorem BeI16.Insts.RusthammerParserInputI16.parse_with_lift (self : BeI16) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  BeI16.Insts.RusthammerEvalInputBackendI16.eval self () input cursor context = (do
    let outcome ← BeI16.Insts.RusthammerParserInputI16.parse_with self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (BeI16.Insts.RusthammerParserInputI16 ) self input cursor context

@[direct_lift] theorem BeI32.Insts.RusthammerParserInputI32.parse_with_lift (self : BeI32) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  BeI32.Insts.RusthammerEvalInputBackendI32.eval self () input cursor context = (do
    let outcome ← BeI32.Insts.RusthammerParserInputI32.parse_with self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (BeI32.Insts.RusthammerParserInputI32 ) self input cursor context

@[direct_lift] theorem BeI64.Insts.RusthammerParserInputI64.parse_with_lift (self : BeI64) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  BeI64.Insts.RusthammerEvalInputBackendI64.eval self () input cursor context = (do
    let outcome ← BeI64.Insts.RusthammerParserInputI64.parse_with self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (BeI64.Insts.RusthammerParserInputI64 ) self input cursor context

@[direct_lift] theorem ByteIn.Insts.RusthammerParserInputU8.parse_with_lift (self : ByteIn) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  ByteIn.Insts.RusthammerEvalInputBackendU8.eval self () input cursor context = (do
    let outcome ← ByteIn.Insts.RusthammerParserInputU8.parse_with self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (ByteIn.Insts.RusthammerParserInputU8 ) self input cursor context

@[direct_lift] theorem ByteNotIn.Insts.RusthammerParserInputU8.parse_with_lift (self : ByteNotIn) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  ByteNotIn.Insts.RusthammerEvalInputBackendU8.eval self () input cursor context = (do
    let outcome ← ByteNotIn.Insts.RusthammerParserInputU8.parse_with self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (ByteNotIn.Insts.RusthammerParserInputU8 ) self input cursor context

@[direct_lift] theorem BytePattern.Insts.RusthammerParserInputSharedPatternSliceU8.parse_with_lift (self : BytePattern) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  BytePattern.Insts.RusthammerEvalInputBackendSharedSliceU8.eval self () input cursor context = (do
    let outcome ← BytePattern.Insts.RusthammerParserInputSharedPatternSliceU8.parse_with self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (BytePattern.Insts.RusthammerParserInputSharedPatternSliceU8 ) self input cursor context

@[direct_lift] theorem Epsilon.Insts.RusthammerParserInputTuple.parse_with_lift (self : Epsilon) (s : Slice Std.U8) (cursor : Cursor) (pc : ParseContext) :
  Epsilon.Insts.RusthammerEvalInputBackendTuple.eval self () s cursor pc = (do
    let outcome ← Epsilon.Insts.RusthammerParserInputTuple.parse_with self s cursor pc
    ok (outcome, ())) := by
  exact eval_direct (Epsilon.Insts.RusthammerParserInputTuple ) self s cursor pc

@[direct_lift] theorem Fail.Insts.RusthammerParser.parse_with_lift {T : Type} (self : Fail T) (s : Slice Std.U8) (c : Cursor)
  (pc : ParseContext) :
  Fail.Insts.RusthammerEval.eval self () s c pc = (do
    let outcome ← Fail.Insts.RusthammerParser.parse_with self s c pc
    ok (outcome, ())) := by
  exact eval_direct (Fail.Insts.RusthammerParser T) self s c pc

@[direct_lift] theorem Bind.Insts.RusthammerParser.parse_with_lift {P : Type} {F : Type} {Q : Type} {Clause0_Output : Type} {Clause2_Output :
  Type} (ParserInst : DirectParser P Clause0_Output)
  (coreopsfunctionFnFTupleClause0_OutputQInst : core.ops.function.Fn F
  Clause0_Output Q) (ParserInst1 : DirectParser Q Clause2_Output) (self : Bind P F)
  (input : Slice Std.U8) (cursor : Cursor) (context : ParseContext) :
  Bind.Insts.RusthammerEval.eval ParserInst coreopsfunctionFnFTupleClause0_OutputQInst ParserInst1 self () input cursor context = (do
    let outcome ← Bind.Insts.RusthammerParser.parse_with ParserInst coreopsfunctionFnFTupleClause0_OutputQInst ParserInst1 self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (Bind.Insts.RusthammerParser ParserInst coreopsfunctionFnFTupleClause0_OutputQInst ParserInst1) self input cursor context

@[direct_lift] theorem Left.Insts.RusthammerParser.parse_with_lift {P : Type} {Q : Type} {Clause0_Output : Type} {Clause1_Output : Type}
  (ParserInst : DirectParser P Clause0_Output) (ParserInst1 : DirectParser Q
  Clause1_Output) (self : Left P Q) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Left.Insts.RusthammerEval.eval ParserInst ParserInst1 self () input cursor context = (do
    let outcome ← Left.Insts.RusthammerParser.parse_with ParserInst ParserInst1 self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (Left.Insts.RusthammerParser ParserInst ParserInst1) self input cursor context

@[direct_lift] theorem Right.Insts.RusthammerParser.parse_with_lift {P : Type} {Q : Type} {Clause0_Output : Type} {Clause1_Output : Type}
  (ParserInst : DirectParser P Clause0_Output) (ParserInst1 : DirectParser Q
  Clause1_Output) (self : Right P Q) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Right.Insts.RusthammerEval.eval ParserInst ParserInst1 self () input cursor context = (do
    let outcome ← Right.Insts.RusthammerParser.parse_with ParserInst ParserInst1 self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (Right.Insts.RusthammerParser ParserInst ParserInst1) self input cursor context

@[direct_lift] theorem Middle.Insts.RusthammerParser.parse_with_lift {L : Type} {P : Type} {R : Type} {Clause0_Output : Type} {Clause1_Output :
  Type} {Clause2_Output : Type} (ParserInst : DirectParser L Clause0_Output)
  (ParserInst1 : DirectParser P Clause1_Output) (ParserInst2 : DirectParser R
  Clause2_Output) (self : Middle L P R) (input : Slice Std.U8)
  (cursor : Cursor) (context : ParseContext) :
  Middle.Insts.RusthammerEval.eval ParserInst ParserInst1 ParserInst2 self () input cursor context = (do
    let outcome ← Middle.Insts.RusthammerParser.parse_with ParserInst ParserInst1 ParserInst2 self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (Middle.Insts.RusthammerParser ParserInst ParserInst1 ParserInst2) self input cursor context

@[direct_lift] theorem Ignore.Insts.RusthammerParserInputTuple.parse_with_lift {P : Type} {Clause0_Output : Type} (ParserInst : DirectParser P Clause0_Output)
  (self : Ignore P) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Ignore.Insts.RusthammerEvalInputBackendTuple.eval ParserInst self () input cursor context = (do
    let outcome ← Ignore.Insts.RusthammerParserInputTuple.parse_with ParserInst self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (Ignore.Insts.RusthammerParserInputTuple ParserInst) self input cursor context

@[direct_lift] theorem FoldRepeat.Insts.RusthammerParser.parse_with_lift {P : Type} {I : Type} {F : Type} {R : Type} {Clause0_Output : Type}
  (ParserInst : DirectParser P Clause0_Output) (coreopsfunctionFnITupleRInst :
  core.ops.function.Fn I Unit R) (coreopsfunctionFnFPairRInst :
  core.ops.function.Fn F (R × Clause0_Output) R) (self : FoldRepeat P I F)
  (input : Slice Std.U8) (cursor : Cursor) (context : ParseContext) :
  FoldRepeat.Insts.RusthammerEval.eval ParserInst coreopsfunctionFnITupleRInst coreopsfunctionFnFPairRInst self () input cursor context = (do
    let outcome ← FoldRepeat.Insts.RusthammerParser.parse_with ParserInst coreopsfunctionFnITupleRInst coreopsfunctionFnFPairRInst self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (FoldRepeat.Insts.RusthammerParser ParserInst coreopsfunctionFnITupleRInst coreopsfunctionFnFPairRInst) self input cursor context

@[direct_lift] theorem SepBy.Insts.RusthammerParserInputVec.parse_with_lift {P : Type} {S : Type} {Clause0_Output : Type} {Clause1_Output : Type}
  (ParserInst : DirectParser P Clause0_Output) (ParserInst1 : DirectParser S
  Clause1_Output) (self : SepBy P S) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  SepBy.Insts.RusthammerEvalInputBackendVec.eval ParserInst ParserInst1 self () input cursor context = (do
    let outcome ← SepBy.Insts.RusthammerParserInputVec.parse_with ParserInst ParserInst1 self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (SepBy.Insts.RusthammerParserInputVec ParserInst ParserInst1) self input cursor context

@[direct_lift] theorem FoldSepBy.Insts.RusthammerParser.parse_with_lift {P : Type} {S : Type} {I : Type} {F : Type} {R : Type} {Clause0_Output :
  Type} {Clause1_Output : Type} (ParserInst : DirectParser P Clause0_Output)
  (ParserInst1 : DirectParser S Clause1_Output) (coreopsfunctionFnITupleRInst :
  core.ops.function.Fn I Unit R) (coreopsfunctionFnFPairRInst :
  core.ops.function.Fn F (R × Clause0_Output) R) (self : FoldSepBy P S I F)
  (input : Slice Std.U8) (cursor : Cursor) (context : ParseContext) :
  FoldSepBy.Insts.RusthammerEval.eval ParserInst ParserInst1 coreopsfunctionFnITupleRInst coreopsfunctionFnFPairRInst self () input cursor context = (do
    let outcome ← FoldSepBy.Insts.RusthammerParser.parse_with ParserInst ParserInst1 coreopsfunctionFnITupleRInst coreopsfunctionFnFPairRInst self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (FoldSepBy.Insts.RusthammerParser ParserInst ParserInst1 coreopsfunctionFnITupleRInst coreopsfunctionFnFPairRInst) self input cursor context

@[direct_lift] theorem TryMap.Insts.RusthammerParser.parse_with_lift {P : Type} {F : Type} {O : Type} {E : Type} {Clause0_Output : Type}
  (ParserInst : DirectParser P Clause0_Output)
  (coreopsfunctionFnFTupleClause0_OutputResultInst : core.ops.function.Fn F
  Clause0_Output (core.result.Result O E)) (self : TryMap P F)
  (input : Slice Std.U8) (cursor : Cursor) (context : ParseContext) :
  TryMap.Insts.RusthammerEval.eval ParserInst coreopsfunctionFnFTupleClause0_OutputResultInst self () input cursor context = (do
    let outcome ← TryMap.Insts.RusthammerParser.parse_with ParserInst coreopsfunctionFnFTupleClause0_OutputResultInst self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (TryMap.Insts.RusthammerParser ParserInst coreopsfunctionFnFTupleClause0_OutputResultInst) self input cursor context

@[direct_lift] theorem Verify.Insts.RusthammerParser.parse_with_lift {P : Type} {F : Type} {Clause0_Output : Type} (ParserInst : DirectParser P
  Clause0_Output) (coreopsfunctionFnFTupleSharedInputClause0_OutputBoolInst :
  core.ops.function.Fn F Clause0_Output Bool) (self : Verify P F)
  (input : Slice Std.U8) (cursor : Cursor) (context : ParseContext) :
  Verify.Insts.RusthammerEval.eval ParserInst coreopsfunctionFnFTupleSharedInputClause0_OutputBoolInst self () input cursor context = (do
    let outcome ← Verify.Insts.RusthammerParser.parse_with ParserInst coreopsfunctionFnFTupleSharedInputClause0_OutputBoolInst self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (Verify.Insts.RusthammerParser ParserInst coreopsfunctionFnFTupleSharedInputClause0_OutputBoolInst) self input cursor context

@[direct_lift] theorem IntRange.Insts.RusthammerParser.parse_with_lift {P : Type} {T : Type} (ParserInst : DirectParser P T) (corecmpOrdInst :
  core.cmp.Ord T) (self : IntRange P T) (input : Slice Std.U8)
  (cursor : Cursor) (context : ParseContext) :
  IntRange.Insts.RusthammerEval.eval ParserInst corecmpOrdInst self () input cursor context = (do
    let outcome ← IntRange.Insts.RusthammerParser.parse_with ParserInst corecmpOrdInst self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (IntRange.Insts.RusthammerParser ParserInst corecmpOrdInst) self input cursor context

@[direct_lift] theorem ButNot.Insts.RusthammerParser.parse_with_lift {P : Type} {Q : Type} {Clause0_Output : Type} {Clause1_Output : Type}
  (ParserInst : DirectParser P Clause0_Output) (ParserInst1 : DirectParser Q
  Clause1_Output) (self : ButNot P Q) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  ButNot.Insts.RusthammerEval.eval ParserInst ParserInst1 self () input cursor context = (do
    let outcome ← ButNot.Insts.RusthammerParser.parse_with ParserInst ParserInst1 self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (ButNot.Insts.RusthammerParser ParserInst ParserInst1) self input cursor context

@[direct_lift] theorem Difference.Insts.RusthammerParser.parse_with_lift {P : Type} {Q : Type} {Clause0_Output : Type} {Clause1_Output : Type}
  (ParserInst : DirectParser P Clause0_Output) (ParserInst1 : DirectParser Q
  Clause1_Output) (self : Difference P Q) (input : Slice Std.U8)
  (cursor : Cursor) (context : ParseContext) :
  Difference.Insts.RusthammerEval.eval ParserInst ParserInst1 self () input cursor context = (do
    let outcome ← Difference.Insts.RusthammerParser.parse_with ParserInst ParserInst1 self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (Difference.Insts.RusthammerParser ParserInst ParserInst1) self input cursor context

@[direct_lift] theorem Xor.Insts.RusthammerParser.parse_with_lift {P : Type} {Q : Type} {Clause0_Output : Type} (ParserInst : DirectParser P
  Clause0_Output) (ParserInst1 : DirectParser Q Clause0_Output) (self : Xor P Q)
  (input : Slice Std.U8) (cursor : Cursor) (context : ParseContext) :
  Xor.Insts.RusthammerEval.eval ParserInst ParserInst1 self () input cursor context = (do
    let outcome ← Xor.Insts.RusthammerParser.parse_with ParserInst ParserInst1 self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (Xor.Insts.RusthammerParser ParserInst ParserInst1) self input cursor context

@[direct_lift] theorem Optional.Insts.RusthammerParserInputOption.parse_with_lift {P : Type} {Clause0_Output : Type} (ParserInst : DirectParser P Clause0_Output)
  (self : Optional P) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Optional.Insts.RusthammerEvalInputBackendOption.eval ParserInst self () input cursor context = (do
    let outcome ← Optional.Insts.RusthammerParserInputOption.parse_with ParserInst self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (Optional.Insts.RusthammerParserInputOption ParserInst) self input cursor context

@[direct_lift] theorem And.Insts.RusthammerParserInputTuple.parse_with_lift {P : Type} {Clause0_Output : Type} (ParserInst : DirectParser P Clause0_Output)
  (self : And P) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  And.Insts.RusthammerEvalInputBackendTuple.eval ParserInst self () input cursor context = (do
    let outcome ← And.Insts.RusthammerParserInputTuple.parse_with ParserInst self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (And.Insts.RusthammerParserInputTuple ParserInst) self input cursor context

@[direct_lift] theorem Not.Insts.RusthammerParserInputTuple.parse_with_lift {P : Type} {Clause0_Output : Type} (ParserInst : DirectParser P Clause0_Output)
  (self : Not P) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  Not.Insts.RusthammerEvalInputBackendTuple.eval ParserInst self () input cursor context = (do
    let outcome ← Not.Insts.RusthammerParserInputTuple.parse_with ParserInst self input cursor context
    ok (outcome, ())) := by
  exact eval_direct (Not.Insts.RusthammerParserInputTuple ParserInst) self input cursor context

@[direct_lift] theorem DirectRun.repeat_parse_lift {P : Type} {Q : Type} {Clause0_Output : Type} (ParserInst : DirectParser P
  Clause0_Output) (ParserInst1 : DirectParser Q Clause0_Output) (parser : P)
  (following : Q) (count : Std.Usize) (input : Slice Std.U8) (cursor : Cursor)
  (context : ParseContext) :
  RustHammer.Code.repeat_parse ParserInst ParserInst1 () parser following count input cursor context = (do
    let outcome ← DirectRun.repeat_parse ParserInst ParserInst1 parser following count input cursor context
    ok (outcome, ())) := by
  unfold DirectRun.repeat_parse
  rw [Std.bind_assoc]
  conv_lhs => rw [← Std.bind_pure (RustHammer.Code.repeat_parse ParserInst ParserInst1 () parser following count input cursor context)]
  apply congrArg (Std.bind _)
  funext ⟨outcome, state⟩
  cases state
  simp [bind_ok]

@[direct_lift] theorem DirectRun.repeat_run_lift {P : Type} {A : Type} {Clause0_Output : Type} {Clause1_Output : Type}
  (ParserInst : DirectParser P Clause0_Output) (RepeatAccumulatorInst :
  RepeatAccumulator A Clause0_Output Clause1_Output) (parser : P)
  (bounds : RepeatBounds) (accumulator : A) (input : Slice Std.U8)
  (cursor : Cursor) (context : ParseContext) :
  RustHammer.Code.repeat_run ParserInst RepeatAccumulatorInst () parser bounds accumulator input cursor context = (do
    let outcome ← DirectRun.repeat_run ParserInst RepeatAccumulatorInst parser bounds accumulator input cursor context
    ok (outcome, ())) := by
  unfold DirectRun.repeat_run
  rw [Std.bind_assoc]
  conv_lhs => rw [← Std.bind_pure (RustHammer.Code.repeat_run ParserInst RepeatAccumulatorInst () parser bounds accumulator input cursor context)]
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
  RustHammer.Code.repeat_run_with ParserInst ParserInst1 RepeatAccumulatorInst () parser following bounds accumulator input cursor context = (do
    let outcome ← DirectRun.repeat_run_with ParserInst ParserInst1 RepeatAccumulatorInst parser following bounds accumulator input cursor context
    ok (outcome, ())) := by
  unfold DirectRun.repeat_run_with
  rw [Std.bind_assoc]
  conv_lhs => rw [← Std.bind_pure (RustHammer.Code.repeat_run_with ParserInst ParserInst1 RepeatAccumulatorInst () parser following bounds accumulator input cursor context)]
  apply congrArg (Std.bind _)
  funext ⟨outcome, state⟩
  cases state
  simp [bind_ok]

@[direct_lift] theorem DirectRun.restrict_match_lift {P : Type} {Q : Type} {Clause0_Output : Type} {Clause1_Output : Type}
  (ParserInst : DirectParser P Clause0_Output) (ParserInst1 : DirectParser Q
  Clause1_Output) (first : P) (second : Q) (input : Slice Std.U8)
  (cursor : Cursor) (context : ParseContext) (allow_equal : Bool) :
  RustHammer.Code.restrict_match ParserInst ParserInst1 () first second input cursor context allow_equal = (do
    let outcome ← DirectRun.restrict_match ParserInst ParserInst1 first second input cursor context allow_equal
    ok (outcome, ())) := by
  unfold DirectRun.restrict_match
  rw [Std.bind_assoc]
  conv_lhs => rw [← Std.bind_pure (RustHammer.Code.restrict_match ParserInst ParserInst1 () first second input cursor context allow_equal)]
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
  RustHammer.Code.match_byte_pattern () pattern input cursor context = (do
    let outcome ← DirectRun.match_byte_pattern pattern input cursor context
    ok (outcome, ())) := by
  unfold DirectRun.match_byte_pattern
  rw [Std.bind_assoc]
  conv_lhs => rw [← Std.bind_pure (RustHammer.Code.match_byte_pattern () pattern input cursor context)]
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
  RustHammer.Code.repeat_run_with_loop ParserInst ParserInst1 RepeatAccumulatorInst () parser following i o accumulator input context unbounded values next count = (do
    let outcome ← DirectRun.repeat_run_with_loop ParserInst ParserInst1 RepeatAccumulatorInst parser following i o accumulator input context unbounded values next count
    ok (outcome, ())) := by
  unfold DirectRun.repeat_run_with_loop
  rw [Std.bind_assoc]
  conv_lhs => rw [← Std.bind_pure (RustHammer.Code.repeat_run_with_loop ParserInst ParserInst1 RepeatAccumulatorInst () parser following i o accumulator input context unbounded values next count)]
  apply congrArg (Std.bind _)
  funext ⟨outcome, state⟩
  cases state
  simp [bind_ok]

@[direct_lift] theorem DirectRun.match_byte_pattern_loop_lift (pattern : Slice Std.U8) (input : Slice Std.U8) (context : ParseContext)
  (next : Cursor) (index : Std.Usize) :
  RustHammer.Code.match_byte_pattern_loop () pattern input context next index = (do
    let outcome ← DirectRun.match_byte_pattern_loop pattern input context next index
    ok (outcome, ())) := by
  unfold DirectRun.match_byte_pattern_loop
  rw [Std.bind_assoc]
  conv_lhs => rw [← Std.bind_pure (RustHammer.Code.match_byte_pattern_loop () pattern input context next index)]
  apply congrArg (Std.bind _)
  funext ⟨outcome, state⟩
  cases state
  simp [bind_ok]

end RustHammer.Code
