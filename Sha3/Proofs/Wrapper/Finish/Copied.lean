import Sha3.Proofs.Wrapper.Finish.Copy
import Sha3.Proofs.Wrapper.Finish.Final
import Sha3.Proofs.Wrapper.Finish.Arguments

namespace Sha3.Proofs.Wrapper.Finish

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

theorem finish_copied [bindings : Bindings] (hStride : UnitStringStride bindings)
    {initial s : RamState} {v : Variant} {mode : Mode} {keccak fullState : Bool} {inputs : Array Input}
    {split : Nat} {state : Incremental.State} {out : BitVec 64}
    (hInitial : ReadyToStep initial)
    (hCall : ValidInvocation bindings v mode initial inputs split keccak fullState)
    (hMode : mode.hasBeforeOutput = true)
    (hInv : Invariant initial v mode s keccak fullState) (hSaved : SavedFrame initial s mode fullState)
    (hRip : s.RIP = startAddress mode v keccak fullState)
    (hRsp : stackPtr s = frameBase initial v mode keccak fullState)
    (hOutput : (outputOperand initial v mode keccak fullState).read s = out)
    (hOut : ValidOutput initial ⟨out.toNat, (v.digestBytes fullState)⟩)
    (hMember : (⟨out.toNat, (v.digestBytes fullState)⟩ : MemoryRegion) ∈
      writeRegions initial v mode keccak fullState)
    (hApart : (⟨out.toNat, (v.digestBytes fullState)⟩ : MemoryRegion).Disjoint
      (Stack.region initial (mode.entry v keccak fullState).minStackBytes))
    (hCursor : state.cursor < v.rate)
    (hMetadata : (Operand.mem (statePointer initial v mode keccak fullState + 200) : Operand 8).read s =
      BitVec.ofNat 8 state.cursor)
    (hLanes : Permutation.memoryLanes (statePointer initial v mode keccak fullState) s = state.lanes) :
    ∃ final, Returns (returnBoundary initial) (49 + ((if fullState then 6352 + 7 + Memcpy.memcpy200Steps out else Finalize.steps v false) + 8)) s final ∧
      Invariant initial v mode final keccak fullState ∧
      (∀ i : Fin (v.digestBytes fullState), final.external[out + BitVec.ofNat 64 i.val]? =
        some (Finalize.digest v state keccak fullState)[i]) ∧
      CalleeSavedRegistersUnchanged initial final ∧
      MemoryWriteFrame s final (finalWrites initial v mode out keccak fullState) := by
  obtain ⟨hd, hs, hApartLayout, hdAlign, hfAlign, hfSmall, hPush⟩ :=
    Copy.layout_bounds mode v keccak fullState hMode
  have hNext : Copy.callPC v mode keccak fullState + (14 : BitVec 64) =
      callAddress mode v keccak fullState := by
    cases mode <;> cases v <;> cases keccak <;> cases fullState <;> first | contradiction | decide +kernel
  obtain ⟨t, hCopy, hInvT, hSavedT, hRipT, hRspT, hRdiT, hRsiT, hMetadataT, hLanesT,
      hMemoryT⟩ := final_copy_steps hStride hCall hMode hInv hSaved hRip hRsp
        (by cases mode <;> first | contradiction | exact hOutput) hMetadata hLanes
  obtain ⟨final, hReturn, hInvFinal, hBytes, hSavedFinal, hMemory⟩ :=
    atCall_returns hStride hInitial hCall
      (by intro he; subst mode; contradiction) (by intro he; subst mode; contradiction)
      hInvT hSavedT (offset := Copy.destinationOffset mode v fullState)
      (by rw [hPush]; omega)
      hdAlign (hRipT.trans hNext) hRspT hRdiT hRsiT hOut hMember hApart hCursor hMetadataT hLanesT
  refine ⟨final, ?_, hInvFinal, hBytes, hSavedFinal, ?_⟩
  · simpa only [← Nat.add_assoc] using hCopy.returns hReturn
  · apply memoryWriteFrame_trans (memoryWriteFrame_mono hMemoryT ?_) hMemory
    intro region hr address ha
    have he : region = Stack.region initial (mode.entry v keccak fullState).minStackBytes := by
      simpa using hr
    subst region
    exact ⟨_, Vector.mem_iff_getElem.mpr ⟨0, by decide, rfl⟩, ha⟩

end Sha3.Proofs.Wrapper.Finish
