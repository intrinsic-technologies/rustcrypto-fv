import P256.Proofs.Verifying.Wrapper.ReturnState
import P256.Proofs.Verifying.Wrapper.KeyCopy.Memory
import P256.Proofs.Program.WrapperMemory

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem copy_frame [Bindings] {initial s t : RamState} {key signature message : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices verifyingKeyVerify initial [key, signature, message] slices)
    (sp : stackPtr s = stackPtr initial-280)
    (ag : AgreesExcept (KeyCopy.components s) s t) :
    MemoryWriteFrame s t (wrapperRegions verifyingKeyVerify initial) := by
  apply ag.memoryWriteFrame
  intro c hc a covered
  simp only [KeyCopy.components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  all_goals try exact covered.elim
  refine ⟨callStack verifyingKeyVerify initial, by simp [wrapperRegions], ?_⟩
  rw [sp] at covered
  exact stack_component_within call.stackAvailable.1 (by decide) (by decide) covered

theorem copy_saved [Bindings] {initial s t : RamState} {key signature message : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices verifyingKeyVerify initial [key, signature, message] slices)
    (sp : stackPtr s = stackPtr initial-280)
    (ag : AgreesExcept (KeyCopy.components s) s t) {offset : Nat} (bound : offset ≤ 40) :
    memLoad t.external (stackPtr initial-BitVec.ofNat 64 offset) 64 =
      memLoad s.external (stackPtr initial-BitVec.ofNat 64 offset) 64 := by
  apply memLoad_agrees_apart ag
  intro a len hc
  have he : a = stackPtr s ∧ len = 65 := by simpa [KeyCopy.components] using hc
  obtain ⟨rfl,rfl⟩ := he
  rw [sp]
  exact stack_sub_apart (a := 280) (b := offset) (na := 65) (nb := 8) call.stackAvailable.1 (by decide) (by change offset ≤ 10280; omega)
    (by decide) (by omega) (Or.inl (by omega))

theorem ReturnState.after_copy [Bindings] {initial s t : RamState} {key signature message : ByteArray}
    {slices : Array Input}
    (state : ReturnState initial s)
    (call : ValidCallWithSlices verifyingKeyVerify initial [key, signature, message] slices)
    (ready : ReadyToStep t) (ag : AgreesExcept (KeyCopy.components s) s t) :
    ReturnState initial t := by
  have frame := copy_frame call state.rsp ag
  refine ⟨bindingsSupported_of_ready_agrees state.bindingsSupported ready ag,
    supportedMachine_of_ready_agrees state.machine ready ag, ?_,
    ag.directionFlagClear (by simp [KeyCopy.components]) state.directionFlag,
    (ag.read (n := 64) (r := 4) (by simp [KeyCopy.components])).trans state.rsp, ?_, ?_,
    (ag.read (n := 64) (r := 5) (by simp [KeyCopy.components])).trans state.rbp,
    fun a ha => ag.grow a (state.allocated a ha)⟩
  · intro a b byte
    rw [frame a]
    · exact state.loaded a b byte
    · intro r hr contained
      have member : r ∈ #v[heapRegion verifyingKeyVerify initial, allocatorStateRegion,
          randomSourceRegion, callStack verifyingKeyVerify initial] := by
        simp_all [wrapperRegions]
      exact (call.separation.2 r member).2 a contained (.inl ⟨b,byte⟩)
  · intro entry member
    have bound : entry.2 ≤ 40 := by
      simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl <;> decide
    exact (copy_saved call state.rsp ag bound).trans (state.saved entry member)
  · have h := copy_saved call state.rsp ag (offset := 0) (by decide)
    change memLoad t.external (stackPtr initial-0#64) 64 =
      memLoad s.external (stackPtr initial-0#64) 64 at h
    simp only [BitVec.sub_zero] at h
    exact h.trans state.returnAddress

end P256.Proofs.Verifying.Wrapper
