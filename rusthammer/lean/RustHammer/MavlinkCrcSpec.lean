import RustHammer.Rusthammer

open Aeneas Aeneas.Std

namespace RustHammer.Mavlink

/-- One reflected CRC-16/MCRF4XX polynomial step, over a mathematical 16-bit word.
The feedback polynomial is 0x8408 (the reflection of 0x1021). -/
def crcBit (word : BitVec 16) : BitVec 16 :=
  if word.getLsbD 0 then (word >>> 1) ^^^ 0x8408#16 else word >>> 1

/-- Apply the polynomial step a specified number of times. -/
def crcRounds : Nat → BitVec 16 → BitVec 16
  | 0, word => word
  | n + 1, word => crcRounds n (crcBit word)

/-- A wire byte enters the low eight positions before eight polynomial steps. -/
def crcByte (word : BitVec 16) (byte : U8) : BitVec 16 :=
  crcRounds 8 (word ^^^ byte.bv.zeroExtend 16)

/-- MAVLink checksums start at 0xffff, include CRC_EXTRA after the transmitted
header/payload bytes, and have no final complement. The caller excludes magic. -/
def crc (bytes : List U8) (extra : U8) : BitVec 16 :=
  crcByte (bytes.foldl crcByte 0xffff#16) extra

end RustHammer.Mavlink
