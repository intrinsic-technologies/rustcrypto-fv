import Sha3.Proofs.Wrapper.Execution.Finish
import Sha3.Proofs.Wrapper.Setup.First

namespace Sha3.Proofs.Wrapper

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

theorem plain_execution_with_update [bindings : Bindings] {initial : RamState} {v : Variant}
    {inputs : Array Input} {split : Nat} {keccak fullState : Bool} {mode : Mode}
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hEnvironment : MachineRamUnitStrideDecodable bindings initial)
    (hCall : ValidInvocation (keccak := keccak) (fullState := fullState) bindings v mode initial inputs split)
    (hUpdate : Loop.UpdateCorrect v (returnBoundary initial))
    (hMode : mode = .plain ∨ mode = .digest := by simp) :
    ∃ fuel final, Returns (returnBoundary initial) fuel initial final ∧
      ExecutionResult (keccak := keccak) (fullState := fullState) v mode initial inputs split final := by
  rcases hMode with rfl | rfl
  · obtain ⟨_, fuel, s, hRun, h⟩ :=
      Setup.plain_through_first_loop hMachine hEnvironment hCall hUpdate
    have hState : Update.StateAt (statePointer (keccak := keccak) (fullState := fullState) initial v .plain)
        (Incremental.canonicalState Keccak.keccakLanes v.rate (message inputs)) s := by
      simpa only [Setup.firstCount, Loop.absorbed, Array.extract_size] using h.state
    obtain ⟨_, final, hReturn, hResult⟩ := finish_execution hEnvironment.stringStride
      (Invariant.initial hMachine hEnvironment hCall).ready hCall h.invariant h.saved
      h.rip h.stack h.output hState (by intro he; cases he)
    exact ⟨_, final, hRun.returns hReturn, hResult⟩
  · obtain ⟨_, fuel, s, hRun, hInv, hSaved, hRip, hStack, hState,
      hOutput, hR12, hPreserved, hMemset⟩ :=
      Setup.digest_through_update hMachine hEnvironment hCall hUpdate
    obtain ⟨_, final, hReturn, hResult⟩ := finish_execution hEnvironment.stringStride
      (Invariant.initial hMachine hEnvironment hCall).ready hCall hInv hSaved
      hRip hStack (by change s.regValue .rbx = initial.regValue .rdx; exact hOutput)
      hState (by intro h; cases h) (fun _ ↦ hPreserved) (fun _ ↦ hR12)
      (fun _ ↦ hMemset)
    exact ⟨_, final, hRun.returns hReturn, hResult⟩

end Sha3.Proofs.Wrapper
