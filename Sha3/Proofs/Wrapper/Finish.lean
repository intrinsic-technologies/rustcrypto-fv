import Sha3.Proofs.Wrapper.Finish.Simple
import Sha3.Proofs.Wrapper.Finish.Copied
import Sha3.Proofs.Wrapper.Finish.Plain

namespace Sha3.Proofs.Wrapper.Finish

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

def steps (v : Variant) (mode : Mode) : Nat :=
  match mode with
  | .plain => plainSteps v
  | .digest => plainSteps v - 3
  | .reset => 3 + (Finalize.steps v false + 8)
  | .finalizeReset | .finalizeFixedReset | .digestFinalizeIntoReset | .digestFinalizeReset => 49 + (Finalize.steps v false + 8)

theorem finish_returns [bindings : Bindings] (hStride : UnitStringStride bindings)
    {initial s : RamState} {v : Variant} {mode : Mode} {keccak fullState : Bool} {inputs : Array Input}
    {split : Nat} {state : Incremental.State} {out : BitVec 64}
    (hInitial : ReadyToStep initial)
    (hCall : ValidInvocation bindings v mode initial inputs split keccak fullState)
    (hInv : Invariant initial v mode s keccak fullState) (hSaved : SavedFrame initial s mode fullState)
    (hRip : s.RIP = startAddress mode v keccak fullState) (hRsp : stackPtr s = frameBase initial v mode keccak fullState)
    (hOutput : (outputOperand initial v mode keccak fullState).read s = out)
    (hOut : ValidOutput initial ⟨out.toNat, (v.digestBytes fullState)⟩)
    (hMember : (⟨out.toNat, (v.digestBytes fullState)⟩ : MemoryRegion) ∈ writeRegions initial v mode keccak fullState)
    (hApart : (⟨out.toNat, (v.digestBytes fullState)⟩ : MemoryRegion).Disjoint
      (Stack.region initial (mode.entry v keccak fullState).minStackBytes))
    (hCursor : state.cursor < v.rate)
    (hMetadata : (Operand.mem (statePointer initial v mode keccak fullState + 200) : Operand 8).read s =
      BitVec.ofNat 8 state.cursor)
    (hLanes : Permutation.memoryLanes (statePointer initial v mode keccak fullState) s = state.lanes)
    (hPreserved : mode = .digest → ∀ j : Fin 6,
      (∀ i : Fin (mode.pushCount fullState),
        (epiloguePopReg mode fullState i).setWidth 5 ≠
          (epiloguePopReg .plain false j).setWidth 5) →
      (Operand.reg ((epiloguePopReg .plain false j).setWidth 5) : Operand 64).read s =
        initial.regValue savedRegisters[j] := by intro h; cases h)
    (hDigestState : mode = .digest → s.regValue .r12 =
      statePointer initial v mode keccak fullState := by intro h; cases h)
    (hDigestMemset : mode = .digest → fullState = true →
      s.regValue .r13 = 0x106a20 := by intro h; cases h) :
    ∃ fuel final, Returns (returnBoundary initial) fuel s final ∧
      Invariant initial v mode final keccak fullState ∧
      (∀ i : Fin (v.digestBytes fullState), final.external[out + BitVec.ofNat 64 i.val]? =
        some (Finalize.digest v state keccak fullState)[i]) ∧
      CalleeSavedRegistersUnchanged initial final ∧
      MemoryWriteFrame s final (finalWrites initial v mode out keccak fullState) := by
  cases mode with
  | reset =>
    obtain ⟨final, hRun, hRest⟩ := finish_simple hStride hInitial hCall hInv hSaved hRip hRsp hOutput
      hOut hMember hApart hCursor hMetadata hLanes
    exact ⟨_, final, hRun, hRest⟩
  | finalizeReset | finalizeFixedReset | digestFinalizeIntoReset | digestFinalizeReset =>
    obtain ⟨final, hRun, hRest⟩ := finish_copied hStride hInitial hCall rfl
      hInv hSaved hRip hRsp hOutput hOut hMember hApart hCursor hMetadata hLanes
    exact ⟨_, final, hRun, hRest⟩
  | plain | digest =>
    cases fullState with
    | false =>
      obtain ⟨final, hRun, hRest⟩ := finish_plain hStride hInitial hCall
        hInv hSaved hRip hRsp hOutput hOut hMember hApart hCursor hMetadata hLanes
        (hMode := by first | exact Or.inl rfl | exact Or.inr rfl)
        (hPreserved := by first
          | exact hPreserved rfl
          | intro j hj; exact (hj j rfl).elim)
        (hDigestState := hDigestState)
      exact ⟨_, final, hRun, hRest⟩
    | true =>
      obtain ⟨rfl, rfl⟩ := hCall.fullState_valid rfl
      exact finish_plain_full hStride hInitial hCall hInv hSaved hRip hRsp hOutput
        hOut hMember hApart hCursor hMetadata hLanes
        (hMode := by first | exact Or.inl rfl | exact Or.inr rfl)
        (hPreserved := by first
          | exact hPreserved rfl
          | intro j hj; exact (hj j rfl).elim)
        (hDigestState := hDigestState)
        (hDigestMemset := fun hm ↦ hDigestMemset hm rfl)

end Sha3.Proofs.Wrapper.Finish
