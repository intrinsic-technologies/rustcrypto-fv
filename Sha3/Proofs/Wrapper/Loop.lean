import Sha3.Proofs.Wrapper.Loop.Prefix
import Sha3.Proofs.Wrapper.Loop.Call
import Sha3.Proofs.Wrapper.Loop.Result
import Sha3.Proofs.Wrapper.Loop.Suffix

namespace Sha3.Proofs.Wrapper.Loop

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

variable {keccak fullState : Bool}

theorem iteration_with_update [bindings : Bindings] {initial s : RamState} {v : Variant}
    {kind : Kind} {inputs : Array Input} {start stop i split : Nat}
    (hCall : ValidInvocation (keccak := keccak) (fullState := fullState) bindings v kind.mode initial inputs split)
    (outside : ¬ InProgram (returnBoundary initial).rip)
    (updateCorrect : UpdateCorrect v (returnBoundary initial))
    (hs : start ≤ i) (hi : i < stop) (hstop : stop ≤ inputs.size)
    (h : State (keccak := keccak) (fullState := fullState) initial v kind inputs start stop i s) (hip : s.RIP = kind.start v (keccak := keccak) (fullState := fullState)) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧
      State (keccak := keccak) (fullState := fullState) initial v kind inputs start stop (i + 1) t ∧
      t.RIP = position kind v (keccak := keccak) (fullState := fullState) (i + 1) stop ∧ AgreesExcept (clobbers (keccak := keccak) (fullState := fullState) initial v kind) s t := by
  have hin : i < inputs.size := by omega
  obtain ⟨prepared, hpRun, hpState, hpRip, hpNext, hpInput, hpLength, hpPointer, hpCursor, hpFrame⟩ :=
    h.prefix hCall outside hip hin
  obtain ⟨called, hcRun, _, hcRegs, hcTop, hcContext, hcFrame⟩ :=
    enter_update hpState hCall hin hpRip hpPointer hpInput hpLength hpCursor
  obtain ⟨fuel, returned, huRun, huReady, _, huResult⟩ :=
    updateCorrect called inputs[i].bytes (absorbed v inputs start i) hcContext
  obtain ⟨huFrame, huRegs, huNext⟩ := after_update hCall.stackAvailable hpState.registers
    hcRegs.stack hcRegs.pointer hcFrame huResult
  have huInv := hpState.invariant.of_agreesExcept hCall huReady huFrame
    (clobbers_writesWithin_outer hCall.stackAvailable) (by exact of_decide_eq_true rfl)
  have huSaved := savedFrame_of_memoryWriteFrame hpState.saved hCall.stackAvailable
    (huFrame.memoryWriteFrame (clobbers_writesWithin hCall.stackAvailable))
    (by change 48 ≤ _; rw [Mode.stackBudget kind.mode v keccak fullState]; omega)
    (fun region hr ↦ (writeRegions_bounds hCall.stackAvailable hr).2)
  have huState : Update.StateAt (statePointer (keccak := keccak) (fullState := fullState) initial v kind.mode)
      (absorbed v inputs start (i + 1)) returned := by
    have hh := huResult.state
    rw [hcRegs.pointer, absorbed_succ v inputs start i hs hin] at hh
    exact hh
  obtain ⟨t, htRun, htState, htRip, htFrame⟩ := finish_iteration hCall outside huInv huSaved
    huRegs huState (huNext.trans hpNext) (huResult.rip.trans hcTop) hi hstop
  exact ⟨_, t, ((hpRun.trans hcRun).trans huRun).trans htRun, htState, htRip,
    clobbers_trans (hpFrame.mono (prefixClobbers_subset initial v kind))
      (clobbers_trans huFrame htFrame)⟩

theorem advance_with_update [bindings : Bindings] {initial s : RamState} {v : Variant}
    {kind : Kind} {inputs : Array Input} {start stop i split : Nat}
    (hCall : ValidInvocation (keccak := keccak) (fullState := fullState) bindings v kind.mode initial inputs split)
    (outside : ¬ InProgram (returnBoundary initial).rip)
    (updateCorrect : UpdateCorrect v (returnBoundary initial))
    (hstart : start ≤ i) (hstop : i ≤ stop) (hsize : stop ≤ inputs.size)
    (h : State (keccak := keccak) (fullState := fullState) initial v kind inputs start stop i s)
    (hip : s.RIP = position kind v (keccak := keccak) (fullState := fullState) i stop) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧
      State (keccak := keccak) (fullState := fullState) initial v kind inputs start stop stop t ∧ t.RIP = kind.exit v (keccak := keccak) (fullState := fullState) ∧
      AgreesExcept (clobbers (keccak := keccak) (fullState := fullState) initial v kind) s t ∧ MemoryWriteFrame s t (writeRegions (keccak := keccak) (fullState := fullState) initial v kind) := by
  obtain ⟨fuel, t, hrun, ht, hrip, hframe⟩ := iterate_range
    (fun i hs hi s h hip ↦ iteration_with_update hCall outside updateCorrect hs hi hsize h hip)
    hstart hstop h hip
  exact ⟨fuel, t, hrun, ht, hrip, hframe,
    hframe.memoryWriteFrame (clobbers_writesWithin hCall.stackAvailable)⟩

end Sha3.Proofs.Wrapper.Loop
