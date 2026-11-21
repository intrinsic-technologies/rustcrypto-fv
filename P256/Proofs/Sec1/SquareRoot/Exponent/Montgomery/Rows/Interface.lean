import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Rows.Common

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Montgomery.Rows

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def savedPtr (s : RamState) : BitVec 64 :=
  (Operand.mem (stackPtr s+24) : Operand 64).read s

structure Saved (s : RamState) (b : Vector (BitVec 64) 4) : Prop where
  b0 : (Operand.mem (stackPtr s+72) : Operand 64).read s = b[0]
  b1 : (Operand.mem (stackPtr s+16) : Operand 64).read s = b[1]
  b2 : (Operand.mem (stackPtr s+88) : Operand 64).read s = b[2]
  b3 : (Operand.mem (stackPtr s+96) : Operand 64).read s = b[3]
  p0 : (Operand.mem (stackPtr s+32) : Operand 64).read s = 0xffffffffffffffff
  p1 : (Operand.mem (stackPtr s+48) : Operand 64).read s = 0xffffffff
  p2 : (Operand.mem (stackPtr s+40) : Operand 64).read s = 0
  p3 : (Operand.mem (stackPtr s+64) : Operand 64).read s = 0xffffffff00000001
  inverse : (Operand.mem (stackPtr s+80) : Operand 64).read s = 1

structure Pre [Bindings] (entry : BitVec 64) (boundary : ReturnBoundary)
    (a b : Vector (BitVec 64) 4) (s : RamState) : Prop where
  entryValid : Entry entry
  rip : s.RIP = entry+0x149#64
  ready : ReadyToStep s
  loaded : ProgramLoaded s
  boundaryOutside : ¬ InProgram boundary.rip
  memory : Reduction.MemoryPre s
  saved : Saved s b
  input : MemReadable s (savedPtr s) 32
  inputApart : RangeApart (stackPtr s) 112 (savedPtr s) 32
  inputWords : ∀ i : Fin 4,
    (Operand.mem (savedPtr s+BitVec.ofNat 64 (8*i.val)) : Operand 64).read s = a[i]
  digit : (Operand.reg 14 : Operand 64).read s = a[1]
  first : (Operand.reg 10 : Operand 64).read s = (firstRow a[0] a[1] b).first
  second : (Operand.reg 3 : Operand 64).read s = (firstRow a[0] a[1] b).second
  low : (Operand.reg 15 : Operand 64).read s = (firstRow a[0] a[1] b).top.low
  mid : (Operand.reg 9 : Operand 64).read s = (firstRow a[0] a[1] b).top.mid
  high : (Operand.mem (stackPtr s+104) : Operand 64).read s = (firstRow a[0] a[1] b).top.high
  carry : (Operand.mem (stackPtr s+7) : Operand 8).read s =
    BitVec.ofNat 8 (firstRow a[0] a[1] b).top.carry.toNat

structure Result [Bindings] (entry : BitVec 64) (boundary : ReturnBoundary)
    (a b : Vector (BitVec 64) 4) (s t : RamState) : Prop where
  advances : ∃ fuel, Advances boundary fuel s t
  ready : ReadyToStep t
  loaded : ProgramLoaded t
  rip : t.RIP = entry+0x430#64
  memory : Reduction.MemoryPre t
  frame : AgreesExcept (Reduction.scratchComponents s) s t
  rsp : stackPtr t = stackPtr s
  rdi : t.regValue .rdi = s.regValue .rdi
  input : Reduction.Input t
    ⟨(multiplyWords a b).first, (multiplyWords a b).second,
      (multiplyWords a b).top.low, (multiplyWords a b).top.mid⟩
    (multiplyWords a b).top.high
  modulus : Reduction.Modulus t Reduction.modulus
  savedHigh : (Operand.reg 10 : Operand 64).read t = (multiplyWords a b).top.highBeforeCarry
  savedCarry : (Operand.mem (stackPtr t+16) : Operand 8).read t =
    BitVec.ofNat 8 (multiplyWords a b).top.carry.toNat

end P256.Proofs.Sec1.SquareRoot.Montgomery.Rows
