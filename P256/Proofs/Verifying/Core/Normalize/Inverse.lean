import P256.Proofs.Verifying.Core.Normalize.InverseSetup
import P256.Proofs.Program.FieldCall.Unary
import P256.Proofs.Field.Inverse.Correct
import P256.Proofs.Projective.Preserve

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Normalize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program
open SecretKeyFromBytes.Scalar (Nat256At)
open Standards.SECG.ECC

def inverseLayout : StackCallLayout 9992 32 40 880 :=
  ⟨1184,1112,280,by decide,by decide,by decide,by decide,by decide,by decide,Or.inl (by decide)⟩

theorem inverse [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {point : Projective} {r : Nat}
    (pre : Core.Pre s boundary) (frame : Frame s t) (rip : t.RIP = 0x10de41)
    (pointAt : ProjectiveAt t (stackPtr s - 1176) point)
    (rAt : Nat256At t (stackPtr s - 472) r) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x10de56 ∧
      ProjectiveAt u (stackPtr s - 1176) point ∧
      Nat256At u (stackPtr s - 472) r ∧
      Field.MontgomeryAt u (stackPtr s - 280) (Curve.inverse Operations.domain.p point.z) ∧
      u.external[stackPtr s - 248]? = some (if point.z = 0 then 0 else 1) ∧
      u.regValue .r15 = stackPtr s - 280 ∧ memLoad u.external (stackPtr s-792) 64 = memLoad t.external (stackPtr s-792) 64 ∧
      MemoryWriteFrame t u #v[ScalarFrame.workRegion s 9992] := by
  obtain ⟨n,a,runA,stateA,effectA,memoryA⟩ := inverse_setup pre frame rip
  have source : a.regValue .rsi = stackPtr s - 1112 := by
    have h := effectA.writes.1
    change a.regValue .rsi = stackPtr t + 64 at h
    rw [h,frame.rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have saved : a.regValue .r15 = stackPtr s - 280 := by
    have h := effectA.writes.2.1
    change a.regValue .r15 = stackPtr t + 896 at h
    rw [h,frame.rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have destination : a.regValue .rdi = stackPtr s - 280 := by
    have h := effectA.writes.2.2
    change a.regValue .rdi = stackPtr t + 896 at h
    rw [h,frame.rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have zAt : Field.MontgomeryAt a (stackPtr s - 1112) point.z := by
    have z := pointAt.2.2
    rw [show stackPtr s - 1176 + 64 = stackPtr s - 1112 by
      simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl] at z
    exact z.of_bytes_eq (fun i hi => by rw [memoryA])
  obtain ⟨m,u,runU,stateU,ripU,value,regs,bytes,memoryU⟩ :=
    FieldCall.unary_call pre.toCalleePre stateA inverseLayout rfl (by decide)
      0xde51 0x623a (by decide) (by decide +kernel) (by decide +kernel)
      (by decide) (inProgram_of_textOffset 0x14090 (by decide))
      (resultAt := fun v address =>
        Field.MontgomeryAt v address (Curve.inverse Operations.domain.p point.z) ∧
        v.external[address+32]? = some (if point.z = 0 then 0 else 1))
      (fun v cp hz => Field.Inverse.inverse_correct cp hz)
      effectA.rip source destination zAt
  refine ⟨n+m,u,runA.trans runU,stateU,ripU,?_,?_,value.1,?_,
    (regs .r15 (by simp)).trans saved,?_,?_⟩
  · apply pointAt.of_bytes_eq
    intro i hi
    exact (bytes 1176 96 (by decide) (by decide) (Or.inr (by decide)) i hi).trans
      (by rw [memoryA]; rfl)
  · exact ⟨rAt.1,fun i hi =>
      ((bytes 472 32 (by decide) (by decide) (Or.inr (by decide)) i hi).trans
        (by rw [memoryA]; rfl)).trans (rAt.2 i hi)⟩
  · have flag := value.2
    change u.external[stackPtr s - 280 + 32]? = _ at flag
    rwa [show stackPtr s - 280 + 32 = stackPtr s - 248 by
      simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl] at flag
  · apply memLoad_congr
    intro i hi
    change (u.external[stackPtr s-792#64+BitVec.ofNat 64 i]?).getD 0 =
      (t.external[stackPtr s-792#64+BitVec.ofNat 64 i]?).getD 0
    rw [bytes 792 8 (by decide) (by decide) (Or.inr (by decide)) i hi,memoryA]
  · intro address outside
    rw [memoryU address outside,memoryA]

end P256.Proofs.Verifying.Core.Normalize
