import P256.Proofs.Generate.Wrapper.State
import P256.Proofs.Program.CalleeStackFrame

set_option autoImplicit false

namespace P256.Proofs.Generate.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program

theorem State.after_callee [Bindings] {initial s t : RamState} {input : ByteArray}
    {slices : Array Input} {offset outputBytes reserve outputOffset : Nat} {written : Option MemoryRegion}
    (call : ValidCallWithSlices signingKeyGenerateFromRng initial [input] slices)
    (state : State initial s (offset+8) written)
    (result : CalleeResult s t (returnBoundary initial) outputBytes reserve)
    (destination : s.regValue .rdi = stackPtr initial - BitVec.ofNat 64 outputOffset)
    (capacity : offset+8+reserve ≤ 4024) (stackBelow : 24 ≤ offset)
    (outputBound : outputOffset ≤ 4024) (outputBelow : outputBytes+24 ≤ outputOffset) :
    State initial t offset written := by
  have memory := result.stack_frame call.stackAvailable.1 state.rsp destination capacity
    (by omega) outputBound outputBelow
  obtain ⟨n, previous⟩ := state.execution
  obtain ⟨fuel, run⟩ := result.execution
  refine ⟨⟨n+fuel, previous.trans run⟩, result.bindingsSupported, result.machine, result.loaded,
    result.directionFlag, ?_,
    (result.calleeSaved .r14 (by simp)).trans state.output,
    (result.calleeSaved .rbx (by simp)).trans state.capacity,
    (work_read call.stackAvailable.1 memory (by decide)).trans state.savedRbx,
    (work_read call.stackAvailable.1 memory (by decide)).trans state.savedR14,
    (work_read call.stackAvailable.1 memory (by decide)).trans state.savedR15,
    ?_, ?_, fun a ha => result.allocated a (state.allocated a ha),
    memoryWriteFrame_trans state.frame (work_frame_regions call.stackAvailable.1 memory written)⟩
  · change t.regValue .rsp = _
    rw [result.rsp]
    change stackPtr s+8 = _
    rw [state.rsp, BitVec.ofNat_add, ← BitVec.sub_sub]
    exact BitVec.sub_add_cancel _ _
  · have h := work_read call.stackAvailable.1 memory (offset := 0) (by decide)
    simp only [BitVec.sub_zero] at h
    exact h.trans state.returnAddress
  · intro r hr
    apply (result.calleeSaved r ?_).trans (state.otherRegisters r hr)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp

end P256.Proofs.Generate.Wrapper
