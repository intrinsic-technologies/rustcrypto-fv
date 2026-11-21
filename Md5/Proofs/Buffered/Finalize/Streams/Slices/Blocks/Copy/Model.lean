import Md5.Proofs.Buffered.Finalize.Streams.Slices.Layout
import Md5.Proofs.Buffered.Finalize.Geometry
import Md5.Proofs.Block.Execution

namespace Md5.Proofs.Buffered.Finalize.Streams.Slices.Blocks.Copy

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

inductive Kind where
  | longTail
  | finalBlock
  deriving DecidableEq

def Kind.entry (kind : Kind) (update : Bool := false) : BitVec 64 :=
  match kind with
  | .longTail => BitVec.ofNat 64 (relocated update 0x10048d)
  | .finalBlock => BitVec.ofNat 64 (relocated update 0x100555)

def Kind.exit (kind : Kind) (update : Bool := false) : BitVec 64 :=
  match kind with
  | .longTail => BitVec.ofNat 64 (relocated update 0x1004f9)
  | .finalBlock => BitVec.ofNat 64 (relocated update 0x1005b4)

def Kind.words : Kind → Nat
  | .longTail => 8
  | .finalBlock => 7

def Kind.length (kind : Kind) : Nat := 8 * kind.words

def Kind.bytes : Kind → List UInt8
  | .longTail =>
    [0x48, 0x8b, 0x44, 0x24, 0x48, 0x48, 0x89, 0x84, 0x24, 0xa0, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x44,
      0x24, 0x40, 0x48, 0x89, 0x84, 0x24, 0x98, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x44, 0x24, 0x38, 0x48,
      0x89, 0x84, 0x24, 0x90, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x44, 0x24, 0x30, 0x48, 0x89, 0x84, 0x24,
      0x88, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x44, 0x24, 0x28, 0x48, 0x89, 0x84, 0x24, 0x80, 0x0, 0x0,
      0x0, 0x48, 0x8b, 0x44, 0x24, 0x20, 0x48, 0x89, 0x44, 0x24, 0x78, 0x48, 0x8b, 0x44, 0x24, 0x10,
      0x48, 0x8b, 0x4c, 0x24, 0x18, 0x48, 0x89, 0x4c, 0x24, 0x70, 0x48, 0x89, 0x44, 0x24, 0x68,
      0x48,
      0x89, 0xe7, 0x48, 0x8d, 0x74, 0x24, 0x68, 0xba, 0x1, 0x0, 0x0, 0x0]
  | .finalBlock =>
    [0x48, 0x8b, 0x44, 0x24, 0x40, 0x48, 0x89, 0x84, 0x24, 0x98, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x44,
      0x24, 0x38, 0x48, 0x89, 0x84, 0x24, 0x90, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x44, 0x24, 0x30, 0x48,
      0x89, 0x84, 0x24, 0x88, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x44, 0x24, 0x28, 0x48, 0x89, 0x84, 0x24,
      0x80, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x44, 0x24, 0x20, 0x48, 0x89, 0x44, 0x24, 0x78, 0x48, 0x8b,
      0x44, 0x24, 0x10, 0x48, 0x8b, 0x4c, 0x24, 0x18, 0x48, 0x89, 0x4c, 0x24, 0x70, 0x48, 0x89,
      0x44,
      0x24, 0x68, 0x48, 0x89, 0xe7, 0x48, 0x8d, 0x74, 0x24, 0x68, 0xba, 0x1, 0x0, 0x0, 0x0]

structure RunPre (kind : Kind) (s : RamState) (update : Bool := false) : Prop extends Storage (streamKind update) s where
  rip : s.RIP = (kind.entry (update := update))

def wordWrite (s : RamState) (word : Nat) : Write :=
  ⟨(.mem (stackPtr s + BitVec.ofNat 64 (104 + 8 * word)) : Operand 64),
    (.mem (stackPtr s + BitVec.ofNat 64 (16 + 8 * word)) : Operand 64).read s⟩

def effect (kind : Kind) (s : RamState) (update : Bool := false) : Effect :=
  { rip := (kind.exit (update := update))
    writes := [
      ⟨(.reg 0 : Operand 64), (.mem (stackPtr s + 16) : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), (.mem (stackPtr s + 24) : Operand 64).read s⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s⟩,
      ⟨(.reg 6 : Operand 64), stackPtr s + 104⟩,
      ⟨(.reg 2 : Operand 64), 1⟩] ++
      (List.range kind.words).map (wordWrite s) }

def changes (kind : Kind) (s : RamState) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 6, .reg 7, .rip, .mem (stackPtr s + 104) kind.length]

inductive Part where
  | high
  | low
  | arguments
  deriving DecidableEq

def Kind.partOffset : Kind → Part → Nat
  | _, .high => 0
  | .longTail, .low => 52
  | .finalBlock, .low => 39
  | .longTail, .arguments => 95
  | .finalBlock, .arguments => 82

def Kind.partLength : Kind → Part → Nat
  | .longTail, .high => 52
  | .finalBlock, .high => 39
  | _, .low => 43
  | _, .arguments => 13

def Kind.partEntry (kind : Kind) (part : Part) (update : Bool := false) : BitVec 64 :=
  (kind.entry (update := update)) + BitVec.ofNat 64 (kind.partOffset part)

def Kind.partBytes (kind : Kind) (part : Part) : List UInt8 :=
  (kind.bytes.drop (kind.partOffset part)).take (kind.partLength part)

structure PartPre (kind : Kind) (part : Part) (s : RamState) (update : Bool := false) : Prop
    extends Storage (streamKind update) s where
  rip : s.RIP = (kind.partEntry part (update := update))

def partEffect (kind : Kind) (part : Part) (s : RamState) (update : Bool := false) : Effect :=
  { rip := (kind.partEntry part (update := update)) + BitVec.ofNat 64 (kind.partLength part)
    writes := match part with
      | .high =>
        [⟨(.reg 0 : Operand 64), (.mem (stackPtr s + 48) : Operand 64).read s⟩,
          wordWrite s 4, wordWrite s 5, wordWrite s 6] ++
          (match kind with | .longTail => [wordWrite s 7] | .finalBlock => [])
      | .low =>
        [⟨(.reg 0 : Operand 64), (.mem (stackPtr s + 16) : Operand 64).read s⟩,
          ⟨(.reg 1 : Operand 64), (.mem (stackPtr s + 24) : Operand 64).read s⟩,
          wordWrite s 0, wordWrite s 1, wordWrite s 2, wordWrite s 3]
      | .arguments =>
        [⟨(.reg 7 : Operand 64), stackPtr s⟩,
          ⟨(.reg 6 : Operand 64), stackPtr s + 104⟩,
          ⟨(.reg 2 : Operand 64), 1⟩] }

end Md5.Proofs.Buffered.Finalize.Streams.Slices.Blocks.Copy
