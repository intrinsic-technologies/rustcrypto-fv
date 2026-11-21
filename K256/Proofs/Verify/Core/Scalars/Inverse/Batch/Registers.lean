import K256.Proofs.Verify.Core.Scalars.Inverse.Batch.State

namespace K256.Proofs.Verify.Core.Scalars.Inverse.Batch

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Verify.LIR
open Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (scalarWords)
open Generate.Generator.Affine.Invert.Core (CalleeFrame CalleeResult signedAt)

open Generate.Generator.Affine.Invert
open SafeGcd.Batch (Words)

def Kept (a b : Registers) := ∀ i : Fin Reg.count, i.val ∈ [4,9,22,39,50,51] → b[i] = a[i]

structure Inner (a : Registers) (w : Words) (left : Nat) : Prop where
  delta : a[12].get 64 = w.delta
  f : a[0].get 64 = w.f
  g : a[1].get 64 = w.g
  u : a[3].get 64 = w.u
  v : a[15].get 64 = w.v
  q : a[6].get 64 = w.q
  r : a[7].get 64 = w.r
  counter : a[2].get 32 = BitVec.ofNat 32 left

structure Rows (a : Registers) (w : Words) : Prop where
  delta : a[12] = ⟨64, w.delta⟩
  u : a[3] = ⟨64, w.u⟩
  v : a[15] = ⟨64, w.v⟩
  q : a[13] = ⟨64, w.q⟩
  r : a[14] = ⟨64, w.r⟩

abbrev count (n : Nat) := min 62 (591 - n)

def setupWrites (sp : Word) : List MemoryRegion :=
  [⟨(base sp + 176).toNat,1⟩, ⟨(base sp + 336).toNat,8⟩]

end K256.Proofs.Verify.Core.Scalars.Inverse.Batch
