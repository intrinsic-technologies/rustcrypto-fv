import P256.Proofs.Verifying.Core.Scalars.FirstSetup.Payload
import P256.Proofs.Verifying.Core.Scalars.ProductCall
import P256.Proofs.Verifying.Core.Scalars.Preserve

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Scalars

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame
open SecretKeyFromBytes.Scalar

theorem first_product [Bindings] {s t : RamState} {boundary : ReturnBoundary} {d w r : Nat}
    (pre : Core.Pre s boundary) (state : Frame s t) (rip : t.RIP = 0x10dca0)
    (pointers : Prepare.Pointers s t)
    (digest : Nat256At t (frameBase s+968) d)
    (inverse : Nat256At t (frameBase s+128) w)
    (savedR : Nat256At t (frameBase s+704) r) :
    ∃ n u, Advances boundary n t u ∧ Frame s u ∧ u.RIP = 0x10dd1d ∧
      Prepare.Pointers s u ∧ Nat256At u (frameBase s+800) (d*w % Operations.domain.n) ∧
      Nat256At u (frameBase s+768) w ∧ Nat256At u (frameBase s+704) r ∧
      MemoryWriteFrame t u (prefixRegions s) := by
  obtain ⟨n,a,runA,stateA,effectA,memoryA⟩ := FirstSetup.run pre state rip
  have inverseA := FirstSetup.copy128 pre state stateA effectA inverse
  have savedA := FirstSetup.copy608 pre state stateA effectA inverse
  have digestA := first_slot state.rsp effectA (by decide) (by decide) (Or.inr (by decide)) digest
  have rA := first_slot state.rsp effectA (by decide) (by decide) (Or.inl (by decide)) savedR
  have pointersA := pointers.after effectA.agrees (by simp [FirstSetup.Block.effect,Effect.components])
  have si : a.regValue .rsi = stackPtr s-208 := by
    have h : a.regValue .rsi = stackPtr t+968 := effectA.writes.2.2.2.1
    rw [h,state.rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have dx : a.regValue .rdx = stackPtr s-1048 := by
    have h : a.regValue .rdx = stackPtr t+128 := effectA.writes.2.2.1
    rw [h,state.rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have di : a.regValue .rdi = stackPtr s-376 := by
    have h : a.regValue .rdi = stackPtr t+800 := effectA.writes.2.2.2.2.1
    rw [h,state.rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have hx : Nat256At a (stackPtr s-208) d := by
    rw [slot_address s 968 (by decide)] at digestA
    exact digestA
  have hy : Nat256At a (stackPtr s-1048) w := by
    change Nat256At a (frameBase s+128#64) w at inverseA
    rw [slot_address s 128 (by decide)] at inverseA
    exact inverseA
  obtain ⟨m,u,runU,stateU,ripU,value,regs,bytes,memory⟩ :=
    product_call pre stateA false effectA.rip si dx di hx hy
  refine ⟨n+m,u,runA.trans runU,stateU,ripU,pointers_saved pointersA regs,?_,
    call_slot bytes (by decide) (Or.inr (by decide)) savedA,
    call_slot bytes (by decide) (Or.inr (by decide)) rA,
    memoryWriteFrame_trans memoryA memory⟩
  change Nat256At u (frameBase s+800#64) (d*w % Operations.domain.n)
  rw [slot_address s 800 (by decide)]
  exact value

end P256.Proofs.Verifying.Core.Scalars
