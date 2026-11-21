import Sha3.Proofs.Wrapper.Finish.Arguments
import Sha3.Proofs.Wrapper.Finish.Final

namespace Sha3.Proofs.Wrapper.Finish

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

theorem finish_simple [bindings : Bindings] (hStride : UnitStringStride bindings)
    {initial s : RamState} {v : Variant} {keccak fullState : Bool} {inputs : Array Input}
    {split : Nat} {state : Incremental.State} {out : BitVec 64}
    (hInitial : ReadyToStep initial)
    (hCall : ValidInvocation bindings v .reset initial inputs split keccak fullState)
    (hInv : Invariant initial v .reset s keccak fullState) (hSaved : SavedFrame initial s .reset fullState)
    (hRip : s.RIP = startAddress .reset v keccak fullState) (hRsp : stackPtr s = frameBase initial v .reset keccak fullState)
    (hOutput : (outputOperand initial v .reset keccak fullState).read s = out)
    (hOut : ValidOutput initial ⟨out.toNat, (v.digestBytes fullState)⟩)
    (hMember : (⟨out.toNat, (v.digestBytes fullState)⟩ : MemoryRegion) ∈ writeRegions initial v .reset keccak fullState)
    (hApart : (⟨out.toNat, (v.digestBytes fullState)⟩ : MemoryRegion).Disjoint
      (Stack.region initial (Mode.reset.entry v keccak fullState).minStackBytes))
    (hCursor : state.cursor < v.rate)
    (hMetadata : (Operand.mem (statePointer initial v .reset keccak fullState + 200) : Operand 8).read s =
      BitVec.ofNat 8 state.cursor)
    (hLanes : Permutation.memoryLanes (statePointer initial v .reset keccak fullState) s = state.lanes) :
    ∃ final, Returns (returnBoundary initial) (3 + ((if fullState then 6352 + 7 + Memcpy.memcpy200Steps out else Finalize.steps v false) + 8)) s final ∧
      Invariant initial v .reset final keccak fullState ∧
      (∀ i : Fin (v.digestBytes fullState), final.external[out + BitVec.ofNat 64 i.val]? =
        some (Finalize.digest v state keccak fullState)[i]) ∧
      CalleeSavedRegistersUnchanged initial final ∧
      MemoryWriteFrame s final (finalWrites initial v .reset out keccak fullState) := by
  obtain ⟨t, hArgs, hInvT, hRipT, hRspT, hStateT, hOutT, hMemoryT, _⟩ :=
    arguments_advance hCall hInv hRip hRsp hOutput
  have hSavedT := hSaved.of_external_eq hMemoryT
  have hOffset : Mode.reset.stateOffset v keccak fullState + 201 ≤ Mode.reset.frameSize v keccak fullState - 48 := by
    cases keccak <;> cases fullState <;> cases v <;> decide +kernel
  have hAligned : Mode.reset.stateOffset v keccak fullState % 8 = 0 := by cases keccak <;> cases fullState <;> cases v <;> decide +kernel
  have hMetadataT : (Operand.mem (statePointer initial v .reset keccak fullState + 200) : Operand 8).read t =
      BitVec.ofNat 8 state.cursor := by
    change memLoad t.external _ 8 = _
    rw [hMemoryT]
    exact hMetadata
  have hLanesT : Permutation.memoryLanes (statePointer initial v .reset keccak fullState) t = state.lanes := by
    change (fun lane ↦ memLoad t.external _ 64) = _
    rw [hMemoryT]
    exact hLanes
  obtain ⟨final, hReturn, hInvFinal, hBytes, hSavedFinal, hMemory⟩ :=
    atCall_returns hStride hInitial hCall (by decide) (by decide) hInvT hSavedT hOffset hAligned hRipT hRspT
      hStateT hOutT hOut hMember hApart hCursor hMetadataT hLanesT
  refine ⟨final, ?_, hInvFinal, hBytes, hSavedFinal, ?_⟩
  · simpa only [← Nat.add_assoc] using hArgs.returns hReturn
  · intro address ha
    rw [hMemory address ha, hMemoryT]

end Sha3.Proofs.Wrapper.Finish
