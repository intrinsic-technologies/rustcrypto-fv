import Md5.Proofs.Buffered.Finalize.Contracts

namespace Md5.Proofs.Buffered

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def digestPreparationChanges (initial : RamState) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10,
    .reg 11, .reg 12, .reg 14, .reg 15, .flags, .rip,
    .mem (BitVec.ofNat 64 (Stack.region initial Digest.minStackBytes).start)
      (Stack.region initial Digest.minStackBytes).size]

structure DigestPrepared [Bindings] (initial : RamState) (boundary : ReturnBoundary)
    (input : ByteArray) (s : RamState) : Prop where
  pre : Finalize.Pre .digest boundary input s
  stack : stackPtr s = stackPtr initial - 296
  output : s.regValue .rbx = initial.regValue .rdx
  savedRbx : (Operand.mem (stackPtr s + 264) : Operand 64).read s = initial.regValue .rbx
  savedR12 : (Operand.mem (stackPtr s + 272) : Operand 64).read s = initial.regValue .r12
  savedR14 : (Operand.mem (stackPtr s + 280) : Operand 64).read s = initial.regValue .r14
  savedR15 : (Operand.mem (stackPtr s + 288) : Operand 64).read s = initial.regValue .r15
  returnSlot : (Operand.mem (stackPtr s + 296) : Operand 64).read s = boundary.rip
  agrees : AgreesExcept (digestPreparationChanges initial) initial s

end Md5.Proofs.Buffered
