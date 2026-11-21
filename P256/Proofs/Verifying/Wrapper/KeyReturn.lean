import P256.Proofs.Verifying.Wrapper.KeyCall
import P256.Proofs.Verifying.Wrapper.Work

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem key_call_saved [Bindings] {initial s t : RamState} {key signature message : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices verifyingKeyVerify initial [key, signature, message] slices)
    (ag : AgreesExcept (keyCallComponents initial) s t) {offset : Nat} (bound : offset ≤ 40) :
    memLoad t.external (stackPtr initial-BitVec.ofNat 64 offset) 64 =
      memLoad s.external (stackPtr initial-BitVec.ofNat 64 offset) 64 := by
  apply memLoad_agrees_apart ag
  intro a len hc
  have eq : a = stackPtr initial-288 ∧ len = 8 := by simpa [keyCallComponents] using hc
  obtain ⟨rfl,rfl⟩ := eq
  exact stack_sub_apart (a := 288) (b := offset) (na := 8) (nb := 8)
    call.stackAvailable.1 (by decide) (by change offset ≤ 10280; omega)
    (by decide) (by omega) (Or.inl (by omega))

theorem key_call_frame [Bindings] {initial s t : RamState} {key signature message : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices verifyingKeyVerify initial [key, signature, message] slices)
    (ag : AgreesExcept (keyCallComponents initial) s t) :
    MemoryWriteFrame s t (wrapperRegions verifyingKeyVerify initial) := by
  apply ag.memoryWriteFrame
  intro c hc a covered
  simp only [keyCallComponents,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact covered.elim
  exact ⟨callStack verifyingKeyVerify initial,by simp [wrapperRegions],
    stack_component_within call.stackAvailable.1 (by decide) (by decide) covered⟩

theorem ReturnState.after_key_result [Bindings] {initial s t u : RamState}
    {key signature message : ByteArray} {slices : Array Input}
    (call : ValidCallWithSlices verifyingKeyVerify initial [key, signature, message] slices)
    (state : ReturnState initial s) (ag : AgreesExcept (keyCallComponents initial) s t)
    (sp : stackPtr t = stackPtr initial-288) (output : t.regValue .rdi = stackPtr initial-208)
    (result : CalleeResult t u (returnBoundary initial) 80 3680) : ReturnState initial u := by
  have frame := result.stack_frame (savedBytes := 40) call.stackAvailable.1 sp output
    (by decide) (by decide) (by decide) (by decide)
  refine ⟨result.bindingsSupported,result.machine,result.loaded,result.directionFlag,?_,?_,?_,?_,
    fun a ha => result.allocated a (ag.grow a (state.allocated a ha))⟩
  · change u.regValue .rsp = _
    rw [result.rsp]
    change stackPtr t+8 = _
    rw [sp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  · intro entry member
    have bound : entry.2 ≤ 40 := by
      simp only [savedRegisters,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl <;> decide
    exact (work_read call.stackAvailable.1 frame bound).trans
      ((key_call_saved call ag bound).trans (state.saved entry member))
  · have a := work_read call.stackAvailable.1 frame (offset := 0) (by decide)
    have b := key_call_saved call ag (offset := 0) (by decide)
    change memLoad u.external (stackPtr initial-0#64) 64 =
      memLoad t.external (stackPtr initial-0#64) 64 at a
    change memLoad t.external (stackPtr initial-0#64) 64 =
      memLoad s.external (stackPtr initial-0#64) 64 at b
    simp only [BitVec.sub_zero] at a b
    exact a.trans (b.trans state.returnAddress)
  · exact (result.calleeSaved .rbp (by simp)).trans
      ((ag.read (n := 64) (r := 5) (by simp [keyCallComponents])).trans state.rbp)

end P256.Proofs.Verifying.Wrapper
