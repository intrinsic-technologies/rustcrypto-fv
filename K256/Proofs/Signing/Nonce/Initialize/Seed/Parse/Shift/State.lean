import K256.Proofs.Signing.Nonce.Initialize.Seed.Parse.State
import K256.Proofs.Common.Tactic
import K256.Proofs.Verify.LIR.Generated.Values

namespace K256.Proofs.Signing.Nonce.Initialize.DigestShift

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open CFG Lift Refine Verify.LIR Verify.Core

def footprint (base : BitVec 64) : List MemoryRegion := [⟨base.toNat,184⟩]

structure Saved (base : BitVec 64) (a : Registers) (m : Ram)
    (returnTag : BitVec 64 := 0x1010ae) : Prop where
  bx : memLoad m (base + 24) 64 = a[3].get 64
  r12 : memLoad m (base + 32) 64 = a[12].get 64
  r13 : memLoad m (base + 40) 64 = a[13].get 64
  r14 : memLoad m (base + 48) 64 = a[14].get 64
  r15 : memLoad m (base + 56) 64 = a[15].get 64
  bp : memLoad m (base + 64) 64 = a[5].get 64
  ret : memLoad m (base + 72) 64 = returnTag

structure Masks (b : Registers) (w : Vector (BitVec 64) 4) : Prop where
  zeroReg : ∀ i : Fin Reg.count, i.val ∈ [0,1,2,5,6,8,9,11,12,14] → b[i] = ⟨64,0⟩
  byte : b[7].get 8 = 0
  width : b[7].width = 64
  w0 : b[10] = ⟨64,w[0]⟩
  w1 : b[3] = ⟨64,w[1]⟩
  w2 : b[15] = ⟨64,w[2]⟩
  w3 : b[13] = ⟨64,w[3]⟩

def FlagsKept (a b : Registers) : Prop :=
  ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → b[i] = a[i]

end K256.Proofs.Signing.Nonce.Initialize.DigestShift
