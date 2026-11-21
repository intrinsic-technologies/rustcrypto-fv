import Md5.Proofs.Buffered.DigestContracts

namespace Md5.Proofs.Buffered.DigestPrepare

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Frame [Bindings] (initial : RamState) (boundary : ReturnBoundary)
    (s : RamState) : Prop where
  ready : ReadyToStep s
  code : CodeIn Extracted.programImage s
  df : Prelude.RFLAGS.DirectionFlagClear s.RFLAGS
  boundaryOutside : ¬ InProgram boundary.rip
  stack : stackPtr s = stackPtr initial - 296
  stackLow : 320 ≤ (stackPtr s).toNat
  stackHigh : (stackPtr s).toNat + 264 < userAddressLimit
  stackAligned : (stackPtr s).toNat % 16 = 0
  stackAllocated : (Finalize.Kind.digest.stackRegion s).Allocated s.external
  stackAvoids : (Finalize.Kind.digest.stackRegion s).Avoids
    (fun address ↦ InProgram address ∨ InPageTables address)
  statePointer : (Operand.reg 14 : Operand 64).read s = stackPtr s + 240
  output : s.regValue .rbx = initial.regValue .rdx
  savedRbx : (Operand.mem (stackPtr s + 264) : Operand 64).read s = initial.regValue .rbx
  savedR12 : (Operand.mem (stackPtr s + 272) : Operand 64).read s = initial.regValue .r12
  savedR14 : (Operand.mem (stackPtr s + 280) : Operand 64).read s = initial.regValue .r14
  savedR15 : (Operand.mem (stackPtr s + 288) : Operand 64).read s = initial.regValue .r15
  returnSlot : (Operand.mem (stackPtr s + 296) : Operand 64).read s = boundary.rip
  agrees : AgreesExcept (digestPreparationChanges initial) initial s

structure Initialized [Bindings] (initial : RamState) (boundary : ReturnBoundary)
    (input : ByteArray) (s : RamState) : Prop extends Frame initial boundary s where
  rip : s.RIP = 0x100067
  absorbed : Absorbed (Finalize.Kind.digest.context s) ByteArray.empty s
  inputPointer : (Operand.reg 6 : Operand 64).read s = initial.regValue .rdi
  inputSize : (Operand.reg 15 : Operand 64).read s = BitVec.ofNat 64 input.size
  inputBytes : (Digest.inputRegion initial input).HasBytes s.external input

end Md5.Proofs.Buffered.DigestPrepare
