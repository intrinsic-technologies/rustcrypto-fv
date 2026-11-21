import Sha1.Proofs.Buffered.Finalize.Contracts

namespace Sha1.Proofs.Buffered

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def digestPreparationChanges (initial : RamState) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10,
    .reg 11, .reg 12, .reg 14, .reg 15, .flags, .rip,
    .mem (BitVec.ofNat 64 (Stack.region initial Digest.minStackBytes).start)
      (Stack.region initial Digest.minStackBytes).size]

namespace DigestPrepare

structure Frame [Bindings] (initial : RamState) (boundary : ReturnBoundary)
    (s : RamState) : Prop where
  ready : ReadyToStep s
  code : CodeIn Extracted.programImage s
  df : Prelude.RFLAGS.DirectionFlagClear s.RFLAGS
  boundaryOutside : ¬ InProgram boundary.rip
  stack : stackPtr s = stackPtr initial - 312
  statePointer : (Operand.reg 14 : Operand 64).read s = stackPtr s + 0x100
  output : s.regValue .rbx = initial.regValue .rdx
  savedRbx : (Operand.mem (stackPtr s + 280) : Operand 64).read s = initial.regValue .rbx
  savedR12 : (Operand.mem (stackPtr s + 288) : Operand 64).read s = initial.regValue .r12
  savedR14 : (Operand.mem (stackPtr s + 296) : Operand 64).read s = initial.regValue .r14
  savedR15 : (Operand.mem (stackPtr s + 304) : Operand 64).read s = initial.regValue .r15
  returnSlot : (Operand.mem (stackPtr s + 312) : Operand 64).read s = boundary.rip
  agrees : AgreesExcept (digestPreparationChanges initial) initial s

structure Initialized [Bindings] (initial : RamState) (boundary : ReturnBoundary)
    (input : ByteArray) (s : RamState) : Prop extends Frame initial boundary s where
  rip : s.RIP = 0x100072
  absorbed : Absorbed (stackPtr s + 0xb8) ByteArray.empty s
  inputPointer : (Operand.reg 6 : Operand 64).read s = initial.regValue .rdi
  inputSize : (Operand.reg 15 : Operand 64).read s = BitVec.ofNat 64 input.size
  inputBytes : (Digest.inputRegion initial input).HasBytes s.external input

end DigestPrepare

structure DigestPrepared [Bindings] (initial : RamState) (boundary : ReturnBoundary)
    (input : ByteArray) (s : RamState) : Prop extends DigestPrepare.Frame initial boundary s where
  pre : Finalize.Pre .digestCopy boundary input s

end Sha1.Proofs.Buffered
