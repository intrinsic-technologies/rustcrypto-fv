import Sha3.Proofs.Wrapper.Finish.Plain.Call
import Sha3.Proofs.Wrapper.Finish.Plain.Prepare
import Sha3.Proofs.Wrapper.Finish.Plain.CopyAll
import Sha3.Proofs.Wrapper.Finish.Plain.Full
import Sha3.Proofs.Wrapper.Finish.Final

namespace Sha3.Proofs.Wrapper.Finish

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

def plainSteps (v : Variant) : Nat :=
  Plain.prepareSteps v + ((1 + Finalize.steps v false) + (Plain.copySteps v + 8))

theorem finish_plain [bindings : Bindings] (hStride : UnitStringStride bindings)
    {initial s : RamState} {v : Variant} {keccak : Bool} {mode : Mode} {inputs : Array Input}
    {split : Nat} {state : Incremental.State} {out : BitVec 64}
    (hInitial : ReadyToStep initial)
    (hCall : ValidInvocation bindings v mode initial inputs split keccak)
    (hInv : Invariant initial v mode s keccak) (hSaved : SavedFrame initial s mode)
    (hRip : s.RIP = startAddress mode v keccak) (hRsp : stackPtr s = frameBase initial v mode keccak)
    (hOutput : (outputOperand initial v mode keccak).read s = out)
    (hOut : ValidOutput initial ⟨out.toNat, v.digestBytes⟩)
    (hMember : (⟨out.toNat, v.digestBytes⟩ : MemoryRegion) ∈ writeRegions initial v mode keccak)
    (hApart : (⟨out.toNat, v.digestBytes⟩ : MemoryRegion).Disjoint
      (Stack.region initial (mode.entry v keccak).minStackBytes))
    (hCursor : state.cursor < v.rate)
    (hMetadata : (Operand.mem (statePointer initial v mode keccak + 200) : Operand 8).read s =
      BitVec.ofNat 8 state.cursor)
    (hLanes : Permutation.memoryLanes (statePointer initial v mode keccak) s = state.lanes)
    (hMode : mode = .plain ∨ mode = .digest := by exact Or.inl rfl)
    (hPreserved : ∀ j : Fin 6,
      (∀ i : Fin mode.pushCount,
        (epiloguePopReg mode false i).setWidth 5 ≠
          (epiloguePopReg .plain false j).setWidth 5) →
      (Operand.reg ((epiloguePopReg .plain false j).setWidth 5) : Operand 64).read s =
        initial.regValue savedRegisters[j] := by intro j h; exact (h j rfl).elim)
    (hDigestState : mode = .digest → s.regValue .r12 = statePointer initial v mode keccak :=
      by intro h; cases h) :
    ∃ final, Returns (returnBoundary initial) (if mode = .digest then plainSteps v - 3 else plainSteps v) s final ∧
      Invariant initial v mode final keccak ∧
      (∀ i : Fin v.digestBytes, final.external[out + BitVec.ofNat 64 i.val]? =
        some (Finalize.digest v state keccak)[i]) ∧
      CalleeSavedRegistersUnchanged initial final ∧
      MemoryWriteFrame s final (finalWrites initial v mode out keccak) := by
  obtain ⟨t, hPrepare, hInvT, hSavedT, hRipT, hRspT, hRdiT, hRsiT,
      hOutT, hMetadataT, hLanesT, hMemoryT, hRegistersT⟩ :=
    Plain.prepare_advance hCall hInv hSaved hRip hRsp hOutput hMetadata hLanes
      (hMode := hMode) (hR12 := hDigestState)
  obtain ⟨u, hCallRun, hInvU, hSavedU, hRipU, hRspU, hOutU, hBytesU, hMemoryU, hRegistersU⟩ :=
    Plain.atCall_advance hStride hMode hInitial hCall hInvT hSavedT hRipT hRspT hRdiT hRsiT
      hOutT hCursor hMetadataT hLanesT
  obtain ⟨w, hCopy, hInvW, hSavedW, hRipW, hRspW, hBytesW, hMemoryW, hRegistersW⟩ :=
    Plain.copy_advance ⟨hCall, hInvU, hSavedU, hRipU, hRspU, hOutU, hOut,
      hMember, hApart, (by
        intro i
        simpa only [BitVec.ofNat_add, BitVec.add_assoc] using hBytesU i), hMode⟩
  have hRegisters : CalleeSavedRegistersUnchanged s w := by
    intro register hr
    exact (hRegistersW register hr).trans
      ((hRegistersU register hr).trans (hRegistersT register hr))
  obtain ⟨final, hReturn, hInvFinal, hMemory, hSavedFinal⟩ :=
    returnFromEpilogue hInitial hCall hInvW hSavedW hRipW hRspW
      (by
        intro j hj
        rw [epiloguePopReg_read .plain false w j]
        have hm : (Mode.plain.savedRegisters false)[j] ∈
            [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15] :=
          (by decide +kernel : ∀ j : Fin 6, (Mode.plain.savedRegisters false)[j] ∈
            [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15]) j
        exact (hRegisters _ hm).trans
          ((epiloguePopReg_read .plain false s j).symm.trans (hPreserved j hj)))
  have hSteps : Plain.prepareSteps v + ((1 + Finalize.steps v false) +
      (Plain.copySteps v mode + (mode.pushCount + 2))) =
      (if mode = .digest then plainSteps v - 3 else plainSteps v) := by
    rcases hMode with rfl | rfl <;> cases v <;> decide +kernel
  refine ⟨final, hSteps ▸ hPrepare.returns (hCallRun.returns (hCopy.returns hReturn)),
    hInvFinal, ?_, hSavedFinal, ?_⟩
  · intro i
    rw [hMemory]
    exact hBytesW i
  · have hStack : ∀ region ∈ #v[Stack.region initial (mode.entry v keccak).minStackBytes],
        ∀ address, region.Contains address →
        ∃ target ∈ finalWrites initial v mode out keccak, target.Contains address := by
      intro region hr address ha
      have he : region = Stack.region initial (mode.entry v keccak).minStackBytes := by
        simpa using hr
      exact ⟨_, Vector.mem_iff_getElem.mpr ⟨0, by decide, rfl⟩, he ▸ ha⟩
    have hFrame := memoryWriteFrame_trans
      (memoryWriteFrame_mono hMemoryT hStack)
      (memoryWriteFrame_trans (memoryWriteFrame_mono hMemoryU hStack) hMemoryW)
    intro address ha
    rw [hMemory]
    exact hFrame address ha

end Sha3.Proofs.Wrapper.Finish
