import P256.Proofs.Verifying.Core.Normalize.CopyX
import P256.Proofs.Verifying.Core.Normalize.CoordinateProducts
import P256.Proofs.Verifying.Core.Normalize.Select

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Normalize

open P256.Spec P256.Spec.Program Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame
open SecretKeyFromBytes.Scalar (Nat256At)
open Standards.SECG.ECC

structure Normalized [Bindings] (s t : RamState) (point : Projective) (r : Nat) : Prop
    extends Frame s t where
  rip : t.RIP = 0x10df44
  x : Field.MontgomeryAt t (stackPtr s-600)
    (point.x * Curve.inverse Operations.domain.p point.z % Operations.domain.p)
  y : Field.MontgomeryAt t (stackPtr s-784)
    (point.y * Curve.inverse Operations.domain.p point.z % Operations.domain.p)
  scalar : Nat256At t (stackPtr s-472) r
  rbp : (t.regValue .rbx).setWidth 8 = if point.z=0 then 0 else 1
  r15 : t.regValue .r15 = stackPtr s-600

set_option maxHeartbeats 800000 in
theorem coordinates [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {point : Projective} {r : Nat} (pre : Core.Pre s boundary)
    (state : Inverted s t point r) :
    ∃ n u, Advances boundary n t u ∧ Normalized s u point r ∧
      memLoad u.external (stackPtr s-792) 64 = memLoad t.external (stackPtr s-792) 64 := by
  obtain ⟨n,a,runA,frameA,ripA,xA,agreesA⟩ :=
    CopyX.run pre state.toFrameState state.rip state.represented.1
  have yT : Field.MontgomeryAt t (stackPtr s-1144) point.y := by
    have addr : stackPtr s-1176+32 = stackPtr s-1144 := by bv_omega
    exact addr ▸ state.represented.2.1
  have yA := yT.of_bytes_eq (copied_bytes agreesA 1144 32 (by decide) (by decide) (Or.inr (by decide)))
  have invA := state.inverse.of_bytes_eq
    (copied_bytes agreesA 80 32 (by decide) (by decide) (Or.inl (by decide)))
  have scalarA : Nat256At a (stackPtr s-472) r :=
    ⟨state.scalar.1,fun i hi => (copied_bytes agreesA 472 32
      (by decide) (by decide) (Or.inl (by decide)) i hi).trans (state.scalar.2 i hi)⟩
  have regsA := copied_regs agreesA
  obtain ⟨m,b,runB,frameB,ripB,xB,r15B,regsB,bytesB⟩ :=
    Coordinates.x_product pre frameA ripA xA invA ((regsA .r14 (by simp)).trans state.r14)
  have yB := yA.of_bytes_eq (bytesB 1144 32 (by decide) (by decide) (Or.inr (by decide)))
  have invB := invA.of_bytes_eq (bytesB 80 32 (by decide) (by decide) (Or.inl (by decide)))
  have scalarB : Nat256At b (stackPtr s-472) r :=
    ⟨scalarA.1,fun i hi => (bytesB 472 32 (by decide) (by decide)
      (Or.inl (by decide)) i hi).trans (scalarA.2 i hi)⟩
  obtain ⟨k,c,runC,frameC,ripC,yC,agreesC⟩ := CopyY.run pre frameB ripB yB
  have xC := xB.of_bytes_eq (copied_bytes agreesC 600 32 (by decide) (by decide) (Or.inl (by decide)))
  have invC := invB.of_bytes_eq
    (copied_bytes agreesC 80 32 (by decide) (by decide) (Or.inl (by decide)))
  have scalarC : Nat256At c (stackPtr s-472) r :=
    ⟨scalarB.1,fun i hi => (copied_bytes agreesC 472 32
      (by decide) (by decide) (Or.inl (by decide)) i hi).trans (scalarB.2 i hi)⟩
  have regsC := copied_regs agreesC
  have r14C : c.regValue .r14 = stackPtr s-80 :=
    (regsC .r14 (by simp)).trans ((regsB .r14 (by simp)).trans
      ((regsA .r14 (by simp)).trans state.r14))
  obtain ⟨l,u,runU,frameU,ripU,yU,regsU,bytesU⟩ :=
    Coordinates.y_product pre frameC ripC yC invC r14C
  refine ⟨n+m+k+l,u,((runA.trans runB).trans runC).trans runU,
    ⟨frameU,ripU,?_,yU,?_,?_,?_⟩,?_⟩
  · exact xC.of_bytes_eq (bytesU 600 32 (by decide) (by decide) (Or.inl (by decide)))
  · exact ⟨scalarC.1,fun i hi => (bytesU 472 32 (by decide) (by decide)
      (Or.inl (by decide)) i hi).trans (scalarC.2 i hi)⟩
  · exact (congrArg (fun x : BitVec 64 => x.setWidth 8)
      ((regsU .rbx (by simp)).trans ((regsC .rbx (by simp)).trans
        ((regsB .rbx (by simp)).trans (regsA .rbx (by simp)))))).trans state.rbp
  · exact (regsU .r15 (by simp)).trans ((regsC .r15 (by simp)).trans r15B)
  · apply memLoad_congr
    intro i hi
    change (u.external[stackPtr s-792#64+BitVec.ofNat 64 i]?).getD 0 =
      (t.external[stackPtr s-792#64+BitVec.ofNat 64 i]?).getD 0
    rw [bytesU 792 8 (by decide) (by decide) (Or.inr (by decide)) i hi,
      copied_bytes agreesC 792 8 (by decide) (by decide) (Or.inl (by decide)) i hi,
      bytesB 792 8 (by decide) (by decide) (Or.inr (by decide)) i hi,
      copied_bytes agreesA 792 8 (by decide) (by decide) (Or.inl (by decide)) i hi]

theorem normalize [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {point : Projective} {r : Nat} (pre : Core.Pre s boundary)
    (frame : Frame s t) (rip : t.RIP = 0x10de41)
    (pointAt : ProjectiveAt t (stackPtr s-1176) point)
    (rAt : Nat256At t (stackPtr s-472) r) :
    ∃ n u, Advances boundary n t u ∧ Normalized s u point r ∧
      memLoad u.external (stackPtr s-792) 64 = memLoad t.external (stackPtr s-792) 64 := by
  obtain ⟨n,a,runA,readyA,rbxA⟩ := invert pre frame rip pointAt rAt
  obtain ⟨m,u,runU,readyU,rbxU⟩ := coordinates pre readyA
  exact ⟨n+m,u,runA.trans runU,readyU,rbxU.trans rbxA⟩

end P256.Proofs.Verifying.Core.Normalize
