import P256.Proofs.Nonce.Initialize.Shift.Result
import P256.Proofs.Nonce.Initialize.Reduce.Arithmetic

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Reduce

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar

structure SelectionReady [Bindings] (initial s : RamState) (boundary : ReturnBoundary)
    (original difference : Nat) (select : Bool) : Prop where
  stage : Stage initial s boundary
  rip : s.RIP = 0x107b57
  secret : memLoad s.external (stackPtr s + 184) 64 = initial.regValue .rsi
  output : memLoad s.external (stackPtr s + 192) 64 = initial.regValue .rdi
  length : memLoad s.external (stackPtr s + 176) 64 = 32
  entropy : memLoad s.external (stackPtr s + 168) 64 = 1
  outputPointer : s.regValue .r14 = initial.regValue .rdi
  buffer : s.regValue .rbp = stackPtr s + 8
  destination : s.regValue .rdi = stackPtr s + 8
  source : s.regValue .rdx = stackPtr s + 104
  leftCount : s.regValue .rsi = 4
  rightCount : s.regValue .rcx = 4
  choice : s.regValue .r8 = if select then 1 else 0
  difference : Nat256At s (stackPtr s + 8) difference
  original : Nat256At s (stackPtr s + 104) original

structure Selected [Bindings] (initial s : RamState) (boundary : ReturnBoundary)
    (value : Nat) : Prop where
  stage : Stage initial s boundary
  rip : s.RIP = 0x107b5c
  secret : memLoad s.external (stackPtr s + 184) 64 = initial.regValue .rsi
  output : memLoad s.external (stackPtr s + 192) 64 = initial.regValue .rdi
  length : memLoad s.external (stackPtr s + 176) 64 = 32
  entropy : memLoad s.external (stackPtr s + 168) 64 = 1
  outputPointer : s.regValue .r14 = initial.regValue .rdi
  buffer : s.regValue .rbp = stackPtr s + 8
  value : Nat256At s (stackPtr s + 8) value

end P256.Proofs.Nonce.Initialize.Reduce
