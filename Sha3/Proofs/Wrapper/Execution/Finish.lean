import Sha3.Proofs.Wrapper.Finish
import Sha3.Proofs.Wrapper.Regions

namespace Sha3.Proofs.Wrapper

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

theorem finish_execution [bindings : Bindings] (hstride : UnitStringStride bindings)
    {initial s : RamState} {v : Variant} {mode : Mode} {inputs : Array Input} {split : Nat}
    {keccak fullState : Bool}
    (hInitial : ReadyToStep initial)
    (hCall : ValidInvocation bindings v mode initial inputs split keccak fullState)
    (hInv : Invariant initial v mode s keccak fullState) (hSaved : SavedFrame initial s mode fullState)
    (hRip : s.RIP = Finish.startAddress mode v keccak fullState) (hRsp : stackPtr s = frameBase initial v mode keccak fullState)
    (hOutput : (Finish.outputOperand initial v mode keccak fullState).read s = outputAddress initial mode)
    (hState : Update.StateAt (statePointer initial v mode keccak fullState)
      (Incremental.canonicalState Keccak.keccakLanes v.rate
        (message (afterInputs mode inputs split))) s)
    (hBefore : mode.hasBeforeOutput = true →
      readOutput (mode.entry v keccak fullState) initial s =
        .ok (expectedBeforeDigest v inputs split mode keccak fullState))
    (hPreserved : mode = .digest → ∀ j : Fin 6,
      (∀ i : Fin (mode.pushCount fullState),
        (Finish.epiloguePopReg mode fullState i).setWidth 5 ≠
          (Finish.epiloguePopReg .plain false j).setWidth 5) →
      (Operand.reg ((Finish.epiloguePopReg .plain false j).setWidth 5) : Operand 64).read s =
        initial.regValue savedRegisters[j] := by intro h; cases h)
    (hDigestState : mode = .digest → s.regValue .r12 =
      statePointer initial v mode keccak fullState := by intro h; cases h)
    (hDigestMemset : mode = .digest → fullState = true →
      s.regValue .r13 = 0x106a20 := by intro h; cases h) :
    ∃ fuel final, Returns (returnBoundary initial) fuel s final ∧
      ExecutionResult v mode initial inputs split final keccak fullState := by
  have hOut : ValidOutput initial ⟨(outputAddress initial mode).toNat, (v.digestBytes fullState)⟩ := by
    rw [← outputRegion_eq initial v mode keccak fullState]
    exact hCall.outputWritable
  have hMember : (⟨(outputAddress initial mode).toNat, (v.digestBytes fullState)⟩ : MemoryRegion) ∈
      writeRegions initial v mode keccak fullState := by
    rw [← outputRegion_eq initial v mode keccak fullState]
    exact output_mem_writeRegions initial v mode keccak fullState
  have hApart : (⟨(outputAddress initial mode).toNat, (v.digestBytes fullState)⟩ : MemoryRegion).Disjoint
      (Stack.region initial (mode.entry v keccak fullState).minStackBytes) := by
    rw [← outputRegion_eq initial v mode keccak fullState]
    exact output_stack_disjoint hCall
  obtain ⟨fuel, final, hReturn, hInvFinal, hBytes, hSavedFinal, hMemory⟩ :=
    Finish.finish_returns hstride hInitial hCall hInv hSaved hRip hRsp hOutput
      hOut hMember hApart (Nat.mod_lt _ v.rate_pos) (metadata_of_stateAt hState) hState.lanes hPreserved hDigestState hDigestMemset
  refine ⟨fuel, final, hReturn, hInvFinal, output_of_canonical_at_address hBytes, ?_, hSavedFinal⟩
  intro hMode
  rw [readOutput, readOutput_of_memoryWriteFrame (hCall.beforeOutputWritable hMode).2.1 rfl hMemory ?_]
  · exact hBefore hMode
  · intro region hr
    simp only [Finish.finalWrites, Vector.mem_mk, List.mem_toArray, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact before_stack_disjoint hCall hMode
    · rw [← outputRegion_eq initial v mode keccak fullState]
      exact before_after_disjoint hCall hMode

end Sha3.Proofs.Wrapper
