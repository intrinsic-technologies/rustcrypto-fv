import Md5.Proofs.Buffered.FinalizeReset.Contracts
import Md5.Proofs.Block.Execution

namespace Md5.Proofs.Buffered.FinalizeReset.Copy

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

inductive Kind where
  | longTail
  | finalBlock
  deriving DecidableEq

def Kind.entry (kind : Kind) (variant : Variant := .saved) : BitVec 64 :=
  variant.address (match kind with
    | .longTail => 0x1007f0
    | .finalBlock => 0x1008b6)

def Kind.exit (kind : Kind) (variant : Variant := .saved) : BitVec 64 :=
  variant.address (match kind with
    | .longTail => 0x10085e
    | .finalBlock => 0x100917)

def Kind.words : Kind → Nat
  | .longTail => 8
  | .finalBlock => 7

def Kind.length (kind : Kind) : Nat := 8 * kind.words

def commonBytes : List UInt8 :=
  [0x48, 0x8b, 0x44, 0x24, 0x38, 0x48, 0x89, 0x84, 0x24, 0x90, 0, 0, 0,
      0x48, 0x8b, 0x44, 0x24, 0x30, 0x48, 0x89, 0x84, 0x24, 0x88, 0, 0, 0,
      0x48, 0x8b, 0x44, 0x24, 0x28, 0x48, 0x89, 0x84, 0x24, 0x80, 0, 0, 0,
      0x48, 0x8b, 0x44, 0x24, 0x20, 0x48, 0x89, 0x44, 0x24, 0x78,
      0x48, 0x8b, 0x44, 0x24, 0x18, 0x48, 0x89, 0x44, 0x24, 0x70,
      0x48, 0x8b, 0x44, 0x24, 0x08, 0x48, 0x8b, 0x4c, 0x24, 0x10,
      0x48, 0x89, 0x4c, 0x24, 0x68, 0x48, 0x89, 0x44, 0x24, 0x60,
      0x48, 0x8d, 0xbc, 0x24, 0xe8, 0, 0, 0,
      0x48, 0x8d, 0x74, 0x24, 0x60, 0xba, 1, 0, 0, 0]


def Kind.bytes : Kind → List UInt8
  | .longTail =>
    [0x48, 0x8b, 0x44, 0x24, 0x40, 0x48, 0x89, 0x84, 0x24, 0x98, 0, 0, 0] ++
      commonBytes
  | .finalBlock => commonBytes

structure RunPre (kind : Kind) (s : RamState) (variant : Variant := .saved) : Prop extends Storage s variant where
  rip : s.RIP = kind.entry variant

def wordWrite (s : RamState) (word : Nat) : Write :=
  ⟨(.mem (stackPtr s + BitVec.ofNat 64 (96 + 8 * word)) : Operand 64),
    (.mem (stackPtr s + BitVec.ofNat 64 (8 + 8 * word)) : Operand 64).read s⟩

def effect (kind : Kind) (s : RamState) (variant : Variant := .saved) : Effect :=
  { rip := kind.exit variant
    writes := [
      ⟨(.reg 0 : Operand 64), (.mem (stackPtr s + 8) : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), (.mem (stackPtr s + 16) : Operand 64).read s⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 0xe8⟩,
      ⟨(.reg 6 : Operand 64), stackPtr s + 0x60⟩,
      ⟨(.reg 2 : Operand 64), 1⟩] ++
      (List.range kind.words).map (wordWrite s) }

def changes (kind : Kind) (s : RamState) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 6, .reg 7, .rip, .mem (stackPtr s + 96) kind.length]

inductive Part where
  | high
  | low
  | arguments
  deriving DecidableEq

def Kind.partOffset : Kind → Part → Nat
  | _, .high => 0
  | .longTail, .low => 52
  | .finalBlock, .low => 39
  | .longTail, .arguments => 92
  | .finalBlock, .arguments => 79

def Kind.partLength : Kind → Part → Nat
  | .longTail, .high => 52
  | .finalBlock, .high => 39
  | _, .low => 40
  | _, .arguments => 18

def Kind.partEntry (kind : Kind) (part : Part) (variant : Variant := .saved) : BitVec 64 :=
  kind.entry variant + BitVec.ofNat 64 (kind.partOffset part)

def Kind.partBytes (kind : Kind) (part : Part) : List UInt8 :=
  (kind.bytes.drop (kind.partOffset part)).take (kind.partLength part)

structure PartPre (kind : Kind) (part : Part) (s : RamState) (variant : Variant := .saved) : Prop extends Storage s variant where
  rip : s.RIP = kind.partEntry part variant

def partEffect (kind : Kind) (part : Part) (s : RamState) (variant : Variant := .saved) : Effect :=
  { rip := kind.partEntry part variant + BitVec.ofNat 64 (kind.partLength part)
    writes := match part with
      | .high =>
        [⟨(.reg 0 : Operand 64), (.mem (stackPtr s + 40) : Operand 64).read s⟩,
          wordWrite s 4, wordWrite s 5, wordWrite s 6] ++
          (match kind with | .longTail => [wordWrite s 7] | .finalBlock => [])
      | .low =>
        [⟨(.reg 0 : Operand 64), (.mem (stackPtr s + 8) : Operand 64).read s⟩,
          ⟨(.reg 1 : Operand 64), (.mem (stackPtr s + 16) : Operand 64).read s⟩,
          wordWrite s 0, wordWrite s 1, wordWrite s 2, wordWrite s 3]
      | .arguments =>
        [⟨(.reg 7 : Operand 64), stackPtr s + 0xe8⟩,
          ⟨(.reg 6 : Operand 64), stackPtr s + 0x60⟩,
          ⟨(.reg 2 : Operand 64), 1⟩] }

end Md5.Proofs.Buffered.FinalizeReset.Copy
