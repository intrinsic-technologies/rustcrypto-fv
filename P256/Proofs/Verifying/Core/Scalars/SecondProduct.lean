import P256.Proofs.Verifying.Core.Scalars.SecondSetup.Run
import P256.Proofs.Verifying.Core.Scalars.ProductCall
import P256.Proofs.Verifying.Core.Scalars.Preserve

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Scalars

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame
open SecretKeyFromBytes.Scalar

theorem second_product [Bindings] {s t : RamState} {boundary : ReturnBoundary} {u1 w r : Nat}
    (pre : Core.Pre s boundary) (state : Frame s t) (rip : t.RIP = 0x10dd1d)
    (pointers : Prepare.Pointers s t)
    (signatureR : Nat256At t (s.regValue .r8) r)
    (first : Nat256At t (frameBase s+800) u1)
    (inverse : Nat256At t (frameBase s+768) w)
    (savedR : Nat256At t (frameBase s+704) r) :
    ∃ n u, Advances boundary n t u ∧ Frame s u ∧ u.RIP = 0x10dd69 ∧
      Prepare.Pointers s u ∧ Nat256At u (frameBase s+800) u1 ∧
      Nat256At u (frameBase s+832) (r*w % Operations.domain.n) ∧
      Nat256At u (frameBase s+704) r ∧ MemoryWriteFrame t u (prefixRegions s) := by
  obtain ⟨n,a,runA,stateA,effectA,rInputA,memoryA⟩ :=
    SecondSetup.copy pre state rip pointers.signature signatureR
  have firstA := second_slot state.rsp effectA (by decide) (by decide) first
  have inverseA := second_slot state.rsp effectA (by decide) (by decide) inverse
  have rA := second_slot state.rsp effectA (by decide) (by decide) savedR
  have pointersA := pointers.after effectA.agrees (by simp [SecondSetup.Block.effect,Effect.components])
  have si : a.regValue .rsi = stackPtr s-1048 := by
    have h : a.regValue .rsi = stackPtr t+128 := effectA.writes.2.2.2.1
    rw [h,state.rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have dx : a.regValue .rdx = stackPtr s-408 := by
    have h : a.regValue .rdx = stackPtr t+768 := effectA.writes.2.2.1
    rw [h,state.rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have di : a.regValue .rdi = stackPtr s-344 := by
    have h : a.regValue .rdi = stackPtr t+832 := effectA.writes.2.2.2.2.1
    rw [h,state.rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have hy : Nat256At a (stackPtr s-408) w := by
    rw [slot_address s 768 (by decide)] at inverseA
    exact inverseA
  obtain ⟨m,u,runU,stateU,ripU,value,regs,bytes,memory⟩ :=
    product_call pre stateA true effectA.rip si dx di rInputA hy
  refine ⟨n+m,u,runA.trans runU,stateU,ripU,pointers_saved pointersA regs,
    call_slot bytes (by decide) (Or.inr (by decide)) firstA,?_,
    call_slot bytes (by decide) (Or.inr (by decide)) rA,
    memoryWriteFrame_trans memoryA memory⟩
  change Nat256At u (frameBase s+832#64) (r*w % Operations.domain.n)
  rw [slot_address s 832 (by decide)]
  exact value

end P256.Proofs.Verifying.Core.Scalars
