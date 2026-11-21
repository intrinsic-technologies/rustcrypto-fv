import P256.Proofs.Verifying.Combination.Naf.Interface
import P256.Proofs.Verifying.Combination.Naf.Machine.LoopState

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Machine.DigitMachine

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar

structure BranchPre [Bindings] (s t : RamState) (i c w : Nat) : Prop extends FrameState s t where
  indexBound : i < 256
  carryBound : c ≤ 1
  windowBound : w ≤ 32
  r12 : t.regValue .r12 = 5
  r13 : t.regValue .r13 = BitVec.ofNat 64 c
  r14 : t.regValue .r14 = BitVec.ofNat 64 i
  r15 : t.regValue .r15 = BitVec.ofNat 64 i
  rbp : t.regValue .rbp = -BitVec.ofNat 64 i
  rdx : t.regValue .rdx = BitVec.ofNat 64 w
  rsi : t.regValue .rsi = s.regValue .rdi
  outputLength : memLoad t.external (stackPtr s-136) 64 = 257
  outputPointer : memLoad t.external (stackPtr s-120) 64 = s.regValue .rdi
  bits : memLoad t.external (stackPtr s-112) 64 = 256
  half : memLoad t.external (stackPtr s-104) 64 = 16
  mask : memLoad t.external (stackPtr s-96) 64 = 31
  byteWindow : memLoad t.external (stackPtr s-124) 32 = 32

def digitRegion (s : RamState) (i len : Nat) : MemoryRegion :=
  ⟨(s.regValue .rdi + BitVec.ofNat 64 i).toNat, len⟩

structure BranchPost [Bindings] (s t u : RamState) (next c i : Nat) (ds : List Int) : Prop
    extends FrameState s u where
  rip : u.RIP = if next < 256 then 0x10f3e7 else 0x10f4da
  r12 : u.regValue .r12 = 5
  r13 : u.regValue .r13 = BitVec.ofNat 64 c
  r14 : u.regValue .r14 = BitVec.ofNat 64 next
  r15 : u.regValue .r15 = BitVec.ofNat 64 next
  rbp : u.regValue .rbp = -BitVec.ofNat 64 next
  bytes : Bytes u.external (s.regValue .rdi + BitVec.ofNat 64 i) ds.length
    (fun j => UInt8.ofNat (BitVec.ofInt 8 ((ds[j]?).getD 0)).toNat)
  memory : MemoryWriteFrame t u #v[digitRegion s i ds.length]

end P256.Proofs.Verifying.Combination.Naf.Machine.DigitMachine
