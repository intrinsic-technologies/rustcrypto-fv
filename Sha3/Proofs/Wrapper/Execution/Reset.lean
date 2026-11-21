import Sha3.Proofs.Wrapper.Execution.Finish
import Sha3.Proofs.Wrapper.Setup.First
import Sha3.Proofs.Wrapper.Reset.Call
import Sha3.Proofs.Wrapper.Reset.Suffix

namespace Sha3.Proofs.Wrapper

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

theorem reset_after_first_with_update [bindings : Bindings]
    (hstride : UnitStringStride bindings) {initial s : RamState} {v : Variant}
    {inputs : Array Input} {split : Nat} {keccak fullState : Bool}
    (hInitial : ReadyToStep initial)
    (hCall : ValidInvocation (keccak := keccak) (fullState := fullState) bindings v .reset initial inputs split)
    (updateCorrect : Loop.UpdateCorrect v (returnBoundary initial))
    (h : Setup.FirstResult (keccak := keccak) (fullState := fullState) initial v .reset inputs split s) :
    ∃ fuel final, Returns (returnBoundary initial) fuel s final ∧
      ExecutionResult (keccak := keccak) (fullState := fullState) v .reset initial inputs split final := by
  obtain ⟨cleared, hcRun, hcInv, hcRip, hcInit, hcFrame⟩ :=
    Reset.reset_steps hstride v hCall h.invariant h.saved h.rip h.stack
  have hcIndex : (Operand.reg 3 : Operand 64).read cleared =
      BitVec.ofNat 64 (min split inputs.size) :=
    (hcFrame.read (n := 64) (r := 3) (by
      simp [Reset.resetChanges, Reset.prepareChanges, initializationChanges, Memset.clobbers])).trans
        (h.bound (by decide))
  have hcCount : (Operand.reg 15 : Operand 64).read cleared = BitVec.ofNat 64 inputs.size := by
    have hh := (hcFrame.read (n := 64) (r := 15) (by
      simp [Reset.resetChanges, Reset.prepareChanges, initializationChanges, Memset.clobbers])).trans h.count
    rw [hh, ← hCall.inputSlices.countArgumentMatchesInputs, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hcPointers : cleared.regValue .r12 = initial.regValue .rdi :=
    (hcFrame.read (n := 64) (r := 12) (by
      simp [Reset.resetChanges, Reset.prepareChanges, initializationChanges, Memset.clobbers])).trans h.pointers
  have hcLengths : cleared.regValue .r14 = initial.regValue .rdx :=
    (hcFrame.read (n := 64) (r := 14) (by
      simp [Reset.resetChanges, Reset.prepareChanges, initializationChanges, Memset.clobbers])).trans h.lengths
  obtain ⟨fuel, t, htRun, htInv, htSaved, htStack, htState, htRip, _, htFrame, _⟩ :=
    Reset.suffix_with_update v false (finalizeMode := .finalizeReset) hCall
      (validInvocation_returnBoundary_bounds hInitial hCall).2 updateCorrect hcInv hcInit
      hcRip hcIndex hcCount hcPointers hcLengths (hbound := hcCount)
  have htOutput : (Finish.outputOperand (keccak := keccak) (fullState := fullState) initial v .reset).read t = outputAddress initial .reset := by
    have hm := initialization_outputSlot (hcFrame.mono (cs' := initializationChanges (keccak := keccak) (fullState := fullState) initial v .reset) (by
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · simp only [Reset.prepareChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl <;>
          simp [initializationChanges, Memset.clobbers]
      · exact hc))
    have hh := (Reset.suffix_outputSlot htFrame).trans (hm.trans h.output)
    simpa only [Finish.outputOperand, outputAddress, outputSlot, Mode.outputSlotOffset,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, Reset.mode, Bool.false_eq_true, ite_false] using hh
  obtain ⟨_, final, hReturn, hResult⟩ := finish_execution hstride hInitial hCall htInv (by cases fullState <;> exact ⟨htSaved.saved, htSaved.returnSlot⟩)
    (htRip.trans (by cases keccak <;> cases fullState <;> cases v <;> rfl)) htStack htOutput htState (by intro hh; cases hh)
  exact ⟨_, final, (hcRun.trans htRun).returns hReturn, hResult⟩

end Sha3.Proofs.Wrapper
