import Md5.Proofs.Buffered.Finalize.Geometry
import Md5.Proofs.Block.Execution

namespace Md5.Proofs.Buffered.Finalize.Digest.Finish.Copy

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def bytes : List UInt8 := [
  0x48, 0x8b, 0x44, 0x24, 0x48, 0x48, 0x89, 0x84, 0x24, 0xa0, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x44,
  0x24, 0x40, 0x48, 0x89, 0x84, 0x24, 0x98, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x44, 0x24, 0x38, 0x48,
  0x89, 0x84, 0x24, 0x90, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x44, 0x24, 0x30, 0x48, 0x89, 0x84, 0x24,
  0x88, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x44, 0x24, 0x28, 0x48, 0x89, 0x84, 0x24, 0x80, 0x0, 0x0,
  0x0, 0x48, 0x8b, 0x44, 0x24, 0x18, 0x48, 0x8b, 0x4c, 0x24, 0x20, 0x48, 0x89, 0x4c, 0x24, 0x78,
  0x48, 0x89, 0x44, 0x24, 0x70, 0x48, 0x8d, 0x7c, 0x24, 0x8, 0x48, 0x8d, 0x74, 0x24, 0x70, 0xba,
  0x1, 0x0, 0x0, 0x0]

def wordWrite (s : RamState) (word : Nat) : Write :=
  ⟨(.mem (stackPtr s + BitVec.ofNat 64 (112 + 8 * word)) : Operand 64),
    (.mem (stackPtr s + BitVec.ofNat 64 (24 + 8 * word)) : Operand 64).read s⟩

def effect (s : RamState) : Effect :=
  { rip := 0x10025b
    writes := [
      ⟨(.reg 0 : Operand 64), (.mem (stackPtr s + 24) : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), (.mem (stackPtr s + 32) : Operand 64).read s⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 8⟩,
      ⟨(.reg 6 : Operand 64), stackPtr s + 112⟩,
      ⟨(.reg 2 : Operand 64), 1⟩] ++
      (List.range 7).map (wordWrite s) }

def changes (s : RamState) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 6, .reg 7, .rip, .mem (stackPtr s + 112) 56]

inductive Part where
  | high
  | low
  | arguments
  deriving DecidableEq

def Part.offset : Part → Nat
  | .high => 0
  | .low => 39
  | .arguments => 85

def Part.length : Part → Nat
  | .high => 39
  | .low => 46
  | .arguments => 15

def Part.entry (part : Part) : BitVec 64 :=
  0x1001f7 + BitVec.ofNat 64 part.offset

def Part.bytes (part : Part) : List UInt8 :=
  (Copy.bytes.drop part.offset).take part.length

structure PartPre (part : Part) (s : RamState) : Prop extends Storage .digest s where
  rip : s.RIP = part.entry

def partEffect (part : Part) (s : RamState) : Effect :=
  { rip := part.entry + BitVec.ofNat 64 part.length
    writes := match part with
      | .high =>
        [⟨(.reg 0 : Operand 64), (.mem (stackPtr s + 56) : Operand 64).read s⟩,
          wordWrite s 4, wordWrite s 5, wordWrite s 6]
      | .low =>
        [⟨(.reg 0 : Operand 64), (.mem (stackPtr s + 24) : Operand 64).read s⟩,
          ⟨(.reg 1 : Operand 64), (.mem (stackPtr s + 32) : Operand 64).read s⟩,
          wordWrite s 0, wordWrite s 1, wordWrite s 2, wordWrite s 3]
      | .arguments =>
        [⟨(.reg 7 : Operand 64), stackPtr s + 8⟩,
          ⟨(.reg 6 : Operand 64), stackPtr s + 112⟩,
          ⟨(.reg 2 : Operand 64), 1⟩] }

end Md5.Proofs.Buffered.Finalize.Digest.Finish.Copy
