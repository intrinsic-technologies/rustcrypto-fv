import K256.Proofs.Signing.Composition.Attempt.Inverse.State


namespace K256.Proofs.Signing.Composition.Attempt.Inverse

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Verify.Core (Registers)
open Generate.Generator.Multiply (scalarWords)
open Generate.Generator.Affine.Invert.Core (CalleeFrame CalleeResult)

abbrev coreSp (s : RamState) := sp s - 104

abbrev wrapperStack := [resume .l105b0f 0x105b0f, resume .l102795 0x102795]

abbrev wrapped (l : LIR.Label) (a : Registers) (m : Ram) : LIR.lifted.State :=
  ⟨⟨l,a,m⟩,wrapperStack⟩

def inverseRegion (s : RamState) : List MemoryRegion := [⟨(sp s-840).toNat,1104⟩]

structure Saved (s : RamState) (m : Ram) : Prop where
  ret : memLoad m (sp s-8) 64 = 0x105b0f
  r15 : memLoad m (sp s-16) 64 = sp s+456
  r13 : memLoad m (sp s-32) 64 = sp s+656
  r12 : memLoad m (sp s-40) 64 = sp s+8
  rbx : memLoad m (sp s-48) 64 = sp s+624

structure Preserved (s : RamState) (a : Registers) : Prop where
  rbx : a[3] = ⟨64,sp s+8⟩
  rbp : a[5] = ⟨64,sp s+192⟩
  df : a[22] = ⟨1,0⟩
  fp : a[39].width = 32 ∧ a[50].width = 16 ∧ a[51].width = 16

structure Unmasked (s : RamState) (a : Registers) (k : Nat) : Prop extends Preserved s a where
  rsp : a[4] = ⟨64,sp s-96⟩
  flag : a[0].get 8 = 1
  w0 : a[14] = ⟨64,(scalarWords (Curve.inverse domain.n k))[0]⟩
  w1 : a[15] = ⟨64,(scalarWords (Curve.inverse domain.n k))[1]⟩
  w2 : a[12] = ⟨64,(scalarWords (Curve.inverse domain.n k))[2]⟩
  w3 : a[13] = ⟨64,(scalarWords (Curve.inverse domain.n k))[3]⟩
  r9 : a[9].width = 64

end K256.Proofs.Signing.Composition.Attempt.Inverse
