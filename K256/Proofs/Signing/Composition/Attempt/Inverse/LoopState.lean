import K256.Proofs.Signing.Composition.Attempt.Inverse.State
import K256.Proofs.Verify.Core.Scalars.Inverse.Arithmetic

namespace K256.Proofs.Signing.Composition.Attempt.Inverse

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
open Common.Field
open Generate.Generator.Affine.Invert.Core (base signedAt roundsBefore batchLabel CalleeResult)
open Verify.Core (Registers)
open Generate.Generator.Affine (Reaches)
open Generate.Generator.Multiply (scalarWords)
open Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1

structure LoopState (entry : Registers) (original : Ram) (sp : Word) (k : Nat)
    (n : Nat) (a : Registers) (m : Ram) (d e : Int) : Prop where
  rsp : a[4] = ⟨64, base sp⟩
  delta : a[5] = ⟨64, BitVec.ofInt 64 (Verify.Core.Scalars.Inverse.model k n).delta⟩
  remaining : a[2] = ⟨64, BitVec.ofNat 64 (591 - n)⟩
  scratch : a[14] = ⟨64, base sp + 16⟩
  kept : ∀ i : Fin Reg.count, i.val ∈ [22, 39, 50, 51] → a[i] = entry[i]
  saved : ∀ (i : Fin Reg.count) (off : Nat),
    (i.val, off) ∈ [(3,48),(5,8),(12,40),(13,32),(14,24),(15,16)] →
      memLoad m (sp - BitVec.ofNat 64 off) 64 = entry[i].get 64
  frame : RamWriteFrame original m [⟨(sp - 736).toNat, 736⟩]
  fValue : signedAt m (base sp + 120) (Verify.Core.Scalars.Inverse.model k n).f
  gValue : signedAt m (base sp + 168) (Verify.Core.Scalars.Inverse.model k n).g
  dValue : signedAt m (base sp + 208) d
  eValue : signedAt m (base sp + 248) e
  dBound : d.natAbs < domain.n
  eBound : e.natAbs < domain.n
  dInvariant : (d * k) % (domain.n : Int) = (Verify.Core.Scalars.Inverse.model k n).f % domain.n
  eInvariant : (e * k) % (domain.n : Int) = (Verify.Core.Scalars.Inverse.model k n).g % domain.n
  originalNonzero : (((memLoad m (base sp + 312) 64 ||| memLoad m (base sp + 296) 64) |||
    memLoad m (base sp + 288) 64) ||| memLoad m (base sp + 304) 64) ≠ 0
  outputPtr : memLoad m (base sp + 320) 64 = sp + 16
  modulusPtr : memLoad m (base sp + 160) 64 = 0x2021a0
  modulusInverse : memLoad m (base sp + 328) 64 = 0xb4f20099aa774ec1

end K256.Proofs.Signing.Composition.Attempt.Inverse
