import P256.Proofs.Verifying.Combination.Naf.Interface
import P256.Proofs.Verifying.Combination.Naf.Machine.Window
import P256.Proofs.Verifying.Combination.Naf.Iterator.Advance.Branch

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Machine

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar

structure WindowPre [Bindings] (s : RamState) (n i c : Nat) (output : BitVec 64) : Prop where
  ready : ReadyToStep s
  loaded : ProgramLoaded s
  rip : s.RIP=0x10f3fe
  first : s.regValue .rax=Iterator.word n (i/64)
  second : s.regValue .rdx=Iterator.word n (i/64+1)
  index : s.regValue .rbx=BitVec.ofNat 64 (i%64)
  width : s.regValue .r12=5
  negative : s.regValue .rbp= -BitVec.ofNat 64 i
  carry : s.regValue .r13=BitVec.ofNat 64 c
  readableMask : MemReadable s (s.regValue .rsp+40) 8
  readableOutput : MemReadable s (s.regValue .rsp+16) 8
  mask : memLoad s.external (s.regValue .rsp+40) 64=31
  outputPointer : memLoad s.external (s.regValue .rsp+16) 64=output
  bound : n<2^256
  indexBound : i<256
  carryBound : c≤1

end P256.Proofs.Verifying.Combination.Naf.Machine
