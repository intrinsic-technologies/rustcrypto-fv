import Md5.Proofs.Block.Control
import Md5.Proofs.Memory.Basic

namespace Md5.Proofs.Block

open Md5.Spec Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs

def LoopRegisters (buffer : Standards.RFC.MD5.Buffer) (s : RamState) : Prop :=
  (Operand.reg 1 : Operand 32).read s = buffer.A ∧
  (Operand.reg 8 : Operand 32).read s = buffer.B ∧
  (Operand.reg 2 : Operand 32).read s = buffer.C ∧
  (Operand.reg 0 : Operand 32).read s = buffer.D

structure LoopData (stack input : BitVec 64) (buffer : Standards.RFC.MD5.Buffer)
    (words : Vector (BitVec 32) 16) (s : RamState) : Prop where
  registers : LoopRegisters buffer s
  stackPointer : s.regValue .rsp = stack
  inputPointer : s.regValue .rsi = input
  frame : Md5.Proofs.Memory.MemWritable s stack 0x88
  readable : MemReadable s input 64
  inputWords : ∀ i : Fin 16,
    (Operand.mem (input + BitVec.ofNat 64 (4 * i.val)) : Operand 32).read s = words[i]
  apart : RangeApart stack 0x88 input 64
  code : ∀ i < 0x88, ¬ InProgram (stack + BitVec.ofNat 64 i)

def loopComponents (stack : BitVec 64) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 7, .reg 8, .reg 9,
    .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15,
    .mem stack 0x60, .mem (stack + 0x70) 0x18, .flags, .rip]

end Md5.Proofs.Block
