import K256.Proofs.Verify.Core.Scalars.Inverse.Arithmetic
import K256.Proofs.Verify.Core.Scalars.Inverse.ZeroGuard
import K256.Proofs.Generate.Generator.Affine.Invert.Core.Callee
import K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch.State
import K256.Proofs.Verify.LIR.Fn109490.Frame

namespace K256.Proofs.Verify.Core.Scalars.Inverse.Batch

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Verify.LIR
open Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (scalarWords)
open Generate.Generator.Affine.Invert.Core (CalleeFrame CalleeResult signedAt)

structure Entry (a : Registers) (m : Ram) (sp : Word) (s : Nat) : Prop extends
    CalleeFrame a m sp (sp + 16) 0x10a0f2 720 33 where
  scalarPtr : a[6].get 64 = sp + 328
  modPtr : a[2].get 64 = 0x2021a0
  invWord : a[1].get 64 = 0xb4f20099aa774ec1
  onePtr : a[8].get 64 = 0x202180
  source : Readable m (sp + 328) 32
  input : WordsAt m (sp + 328) 64 (scalarWords s)
  high : sp.toNat + 360 ≤ 2^32
  positive : 0 < s
  bound : s < domain.n

abbrev base (sp : Word) := sp - 392

structure LoopState (a : Registers) (original : Ram) (sp : Word) (s rounds : Nat)
    (b : Registers) (m : Ram) (d e : Int) : Prop where
  rsp : b[4] = ⟨64, base sp⟩
  delta : b[12] = ⟨64, BitVec.ofInt 64 (Inverse.model s rounds).delta⟩
  remaining : b[6] = ⟨64, BitVec.ofNat 64 (591 - rounds)⟩
  kept : ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → b[i] = a[i]
  saved : ∀ (i : Fin Reg.count) (off : Nat),
    (i.val, off) ∈ [(3,48),(5,8),(12,40),(13,32),(14,24),(15,16)] →
      memLoad m (sp - BitVec.ofNat 64 off) 64 = a[i].get 64
  frame : RamWriteFrame original m [⟨(sp - 720).toNat,720⟩]
  fValue : signedAt m (base sp + 8) (Inverse.model s rounds).f
  gValue : signedAt m (base sp + 48) (Inverse.model s rounds).g
  dValue : signedAt m (base sp + 96) d
  eValue : signedAt m (base sp + 136) e
  dBound : d.natAbs < domain.n
  eBound : e.natAbs < domain.n
  dInvariant : (d * s) % (domain.n : Int) = (Inverse.model s rounds).f % domain.n
  eInvariant : (e * s) % (domain.n : Int) = (Inverse.model s rounds).g % domain.n
  originalNonzero : (((memLoad m (base sp + 280) 64 ||| memLoad m (base sp + 264) 64) |||
    memLoad m (base sp + 256) 64) ||| memLoad m (base sp + 272) 64) ≠ 0
  outputPtr : memLoad m (base sp + 288) 64 = sp + 16
  modulusPtr : memLoad m (base sp + 88) 64 = 0x2021a0
  modulusInverse : memLoad m (base sp + 296) 64 = 0xb4f20099aa774ec1

def Result (a : Registers) (m : Ram) (sp : Word) (s : Nat)
    (out : Output Value Ram Reg.count) : Prop :=
  CalleeResult a m sp (sp + 16) 0x10a0f2 720 33 out ∧
  WordsAt out.store (sp + 16) 64 (scalarWords (Curve.inverse domain.n s)) ∧
  memLoad out.store (sp + 48) 8 = 1

end K256.Proofs.Verify.Core.Scalars.Inverse.Batch
