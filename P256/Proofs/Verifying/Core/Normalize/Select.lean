import P256.Proofs.Verifying.Core.Normalize.Inverse
import P256.Proofs.Verifying.Core.Normalize.SelectPayload
import P256.Proofs.PublicPoint.Normalize.Invert.SelectCall
import P256.Proofs.Projective.Multiply.Machine.Lookup.Select.Correct

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Normalize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program FieldCall
open SecretKeyFromBytes.Scalar (Nat256At)
open Standards.SECG.ECC

def selectInverseSite : BinaryCallSite 9992 1176 0x114380 128 :=
  ⟨0xdea5,0x64d6,by decide,by decide +kernel,by decide +kernel,by decide,
    inProgram_of_textOffset 0x14380 (by decide),
    ⟨1184,312,80,by decide,by decide,by decide,by decide,by decide,by decide,Or.inl (by decide)⟩,
    rfl,by decide,280,by decide,by decide,Or.inl (by decide)⟩

structure Inverted [Bindings] (s t : RamState) (point : Projective) (r : Nat) : Prop
    extends Frame s t where
  rip : t.RIP = 0x10deaa
  represented : ProjectiveAt t (stackPtr s-1176) point
  scalar : Nat256At t (stackPtr s-472) r
  inverse : Field.MontgomeryAt t (stackPtr s-80) (Curve.inverse Operations.domain.p point.z)
  rbp : (t.regValue .rbx).setWidth 8 = if point.z=0 then 0 else 1
  r14 : t.regValue .r14 = stackPtr s-80

theorem select_inverse [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {point : Projective} {r : Nat} (pre : Core.Pre s boundary)
    (state : SelectReady s t point r) :
    ∃ n u, Advances boundary n t u ∧ Inverted s u point r ∧
      memLoad u.external (stackPtr s-792) 64 = memLoad t.external (stackPtr s-792) 64 := by
  let choice := decide (point.z ≠ 0)
  obtain ⟨n,u,run,frame,rip,value,regs,bytes,_⟩ := PublicPoint.Normalize.select_binary_call
    (op := fun x y => if choice then y else x) pre.toCalleePre state.toFrameState
    selectInverseSite
    (fun v cp rcx hx hy => Projective.Multiply.Machine.Lookup.Select.field_select_low8_correct
      cp hx hy (by
        rw [rcx,state.choice]
        by_cases hz : point.z=0 <;> simp [choice,hz]))
    state.rip state.left state.right state.output state.zero state.inverse
  refine ⟨n,u,run,⟨frame,rip,?_,?_,?_,?_,(regs .r14 (by simp)).trans state.r14⟩,
    ?_⟩
  · exact state.represented.of_bytes_eq
      (bytes 1176 96 (by decide) (by decide) (Or.inr (by decide)))
  · exact ⟨state.scalar.1,fun i hi =>
      (bytes 472 32 (by decide) (by decide) (Or.inr (by decide)) i hi).trans (state.scalar.2 i hi)⟩
  · by_cases hz : point.z=0
    · simpa [choice,hz,selectInverseSite,Projective.Algebra.inverse_zero] using value
    · simpa [choice,hz,selectInverseSite] using value
  · exact (congrArg (fun x : BitVec 64 => x.setWidth 8) (regs .rbx (by simp))).trans state.rbp
  · apply memLoad_congr
    intro i hi
    change (u.external[stackPtr s-792#64+BitVec.ofNat 64 i]?).getD 0 =
      (t.external[stackPtr s-792#64+BitVec.ofNat 64 i]?).getD 0
    rw [bytes 792 8 (by decide) (by decide) (Or.inr (by decide)) i hi]

theorem invert [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {point : Projective} {r : Nat} (pre : Core.Pre s boundary)
    (frame : Frame s t) (rip : t.RIP = 0x10de41)
    (pointAt : ProjectiveAt t (stackPtr s-1176) point)
    (rAt : Nat256At t (stackPtr s-472) r) :
    ∃ n u, Advances boundary n t u ∧ Inverted s u point r ∧
      memLoad u.external (stackPtr s-792) 64 = memLoad t.external (stackPtr s-792) 64 := by
  obtain ⟨n,a,runA,frameA,ripA,pointA,rA,valueA,flagA,r15A,rbxA,_⟩ :=
    inverse pre frame rip pointAt rAt
  obtain ⟨m,b,runB,readyB,rbxB⟩ :=
    select_prepare pre frameA ripA pointA rA valueA flagA r15A
  obtain ⟨k,u,runU,readyU,rbxU⟩ := select_inverse pre readyB
  exact ⟨n+m+k,u,(runA.trans runB).trans runU,readyU,(rbxU.trans rbxB).trans rbxA⟩

end P256.Proofs.Verifying.Core.Normalize
