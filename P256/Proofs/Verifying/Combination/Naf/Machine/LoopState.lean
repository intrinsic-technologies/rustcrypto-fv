import P256.Proofs.Verifying.Combination.Naf.Interface
import P256.Proofs.Verifying.Combination.Naf.Machine.Initialize
import P256.Proofs.Verifying.Combination.Naf.Recoding

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Machine

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar

structure LoopState [Bindings] (s t : RamState) (n i k c : Nat) (ds : List Int)
    (pc : BitVec 64 := 0x10f3e7) : Prop
    extends FrameState s t where
  rip : t.RIP = pc
  indexBound : i < 256
  carryBound : c ≤ 1
  cachedIndex : i/64 = k ∨ i/64 = k+1
  dsLength : ds.length = i
  specification : digits n = ds ++ recode (257-i) (256-i) (n/2^i) c
  source : Nat256At t (s.regValue .rdx) n
  output : DigitsAt t (s.regValue .rdi) ds
  iterator : Iterator.StateAt t (stackPtr s-88) (s.regValue .rdx) n k
  r12 : t.regValue .r12 = 5
  r13 : t.regValue .r13 = BitVec.ofNat 64 c
  r14 : t.regValue .r14 = BitVec.ofNat 64 i
  r15 : t.regValue .r15 = BitVec.ofNat 64 i
  rbp : t.regValue .rbp = -BitVec.ofNat 64 i
  outputLength : memLoad t.external (stackPtr s-136) 64 = 257
  outputPointer : memLoad t.external (stackPtr s-120) 64 = s.regValue .rdi
  bits : memLoad t.external (stackPtr s-112) 64 = 256
  half : memLoad t.external (stackPtr s-104) 64 = 16
  mask : memLoad t.external (stackPtr s-96) 64 = 31
  byteWindow : memLoad t.external (stackPtr s-124) 32 = 32

theorem digitsAt_nil {s : RamState} {address : BitVec 64}
    (zeroes : Bytes s.external address 257 (fun _ => 0)) : DigitsAt s address [] := by
  intro i hi
  rw [memLoad_8]
  simp [memByte, PhysicalMemory.read, zeroes i hi]

end P256.Proofs.Verifying.Combination.Naf.Machine
