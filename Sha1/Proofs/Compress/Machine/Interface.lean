import Sha1.Proofs.Common.Instructions.StorePre
import X86Proofs.Program.Execution
import X86Proofs.Instructions.Bswap.Operation

namespace Sha1.Proofs.Compress.Machine

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Sha1.Spec.Program Standards.NIST

abbrev MemWritable := Sha1.Proofs.Common.Instructions.StorePre.MemWritable

def OutsideCompression (address : BitVec 64) : Prop :=
  address.toNat < 0x1024e0 ∨ 0x1036df ≤ address.toNat

def LoopRegisters (H : Vector (BitVec 32) 5) (s : RamState) : Prop :=
  (Operand.reg 11 : Operand 32).read s = H[0] ∧
  (Operand.reg 8 : Operand 32).read s = H[1] ∧
  (Operand.reg 2 : Operand 32).read s = H[2] ∧
  (Operand.reg 10 : Operand 32).read s = H[3] ∧
  (Operand.reg 0 : Operand 32).read s = H[4]

def scratchComponents (stack : BitVec 64) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8,
    .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15,
    .mem stack 128, .mem (stack + 144) 16, .flags, .rip]

structure BlockData (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (M : Vector (BitVec 32) 16) (s : RamState) : Prop where
  registers : LoopRegisters H s
  stackPointer : stackPtr s = stack
  inputPointer : s.regValue .rsi = input
  writable : MemWritable s stack 160
  readable : MemReadable s input 64
  words : ∀ i : Fin 16,
    (Operand.mem (input + BitVec.ofNat 64 (4 * i.val)) : Operand 32).read s = bswapSpec M[i]
  apart : RangeApart stack 160 input 64
  code : ∀ i < 160, ¬ InProgram (stack + BitVec.ofNat 64 i)

def BlockCorrect : Prop :=
  ∀ [Bindings] (boundary : ReturnBoundary) (s : RamState) (stack input : BitVec 64)
    (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16),
    OutsideCompression boundary.rip → ReadyToStep s → CodeIn Extracted.programImage s →
    s.RIP = 0x102530 → BlockData stack input H M s →
    ∃ n t, Advances boundary n s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ t.RIP = 0x1036a2 ∧
      BlockData stack input (SHA1.compress H M) M t ∧
      AgreesExcept (scratchComponents stack) s t

end Sha1.Proofs.Compress.Machine
