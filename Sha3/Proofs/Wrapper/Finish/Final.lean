import Sha3.Proofs.Wrapper.Finish.FinalizeCall
import Sha3.Proofs.Wrapper.Finish.Return
import Sha3.Proofs.Finalize
import Sha3.Proofs.Wrapper.Setup.Initialize
import Sha3.Proofs.Memcpy.Contract

namespace Sha3.Proofs.Wrapper.Finish

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

theorem called_returns [bindings : Bindings] (hStride : UnitStringStride bindings)
    {initial s : RamState} {v : Variant} {keccak fullState : Bool}
    {mode : Mode} {inputs : Array Input} {split offset : Nat}
    {state : Incremental.State} {out : BitVec 64}
    (hInitial : ReadyToStep initial)
    (hCall : ValidInvocation bindings v mode initial inputs split keccak fullState)
    (hInv : Invariant initial v mode s keccak fullState) (hSaved : SavedFrame initial s mode fullState)
    (hOffset : offset + 201 ≤ (mode.frameSize v keccak fullState) - (8 * mode.pushCount fullState)) (hAligned : offset % 8 = 0)
    (hRip : s.RIP = Finalize.entryAddress v false keccak fullState)
    (hRsp : s.regValue .rsp = frameBase initial v mode keccak fullState - 8)
    (hRdi : s.regValue .rdi = frameBase initial v mode keccak fullState + BitVec.ofNat 64 offset)
    (hRsi : s.regValue .rsi = out)
    (hOut : ValidOutput initial ⟨out.toNat, (v.digestBytes fullState)⟩)
    (hMember : (⟨out.toNat, (v.digestBytes fullState)⟩ : MemoryRegion) ∈ writeRegions initial v mode keccak fullState)
    (hApart : (⟨out.toNat, (v.digestBytes fullState)⟩ : MemoryRegion).Disjoint
      (Stack.region initial (mode.entry v keccak fullState).minStackBytes))
    (hCursor : state.cursor < v.rate)
    (hMetadata : (Operand.mem (frameBase initial v mode keccak fullState + BitVec.ofNat 64 offset + 200) :
      Operand 8).read s = BitVec.ofNat 8 state.cursor)
    (hLanes : Permutation.memoryLanes (frameBase initial v mode keccak fullState + BitVec.ofNat 64 offset) s =
      state.lanes)
    (hReturn : stackTop s = epilogueAddress mode v keccak fullState)
    (hPreserved : ∀ j : Fin 6,
      (∀ i : Fin (mode.pushCount fullState),
        (epiloguePopReg mode fullState i).setWidth 5 ≠
          (epiloguePopReg .plain false j).setWidth 5) →
      (Operand.reg ((epiloguePopReg .plain false j).setWidth 5) : Operand 64).read s =
        initial.regValue savedRegisters[j]) :
    ∃ final, Returns (returnBoundary initial) ((if fullState then 6352 + 7 + Memcpy.memcpy200Steps out else Finalize.steps v false) + (mode.pushCount fullState + 2)) s final ∧
      Invariant initial v mode final keccak fullState ∧
      (∀ i : Fin (v.digestBytes fullState), final.external[out + BitVec.ofNat 64 i.val]? =
        some (Finalize.digest v state keccak fullState)[i]) ∧
      CalleeSavedRegistersUnchanged initial final ∧
      MemoryWriteFrame s final (Finalize.writeRegions v s fullState) := by
  have hTarget : InProgram (stackTop s) := by
    rw [hReturn]
    have hCode := epilogueCode_subset mode v keccak fullState
    exact ⟨0x48, hCode _ (by cases mode <;> exact List.mem_cons_self)⟩
  have hContains : ∀ i < (v.digestBytes fullState),
      (⟨out.toNat, (v.digestBytes fullState)⟩ : MemoryRegion).Contains
        (out + BitVec.ofNat 64 i).toNat :=
    fun _ hi ↦ Finalize.region_contains_byte (Nat.le_of_lt hOut.2.1) hi
  have hOutputStack : RangeApart out (v.digestBytes fullState) (Finalize.frameBase s) 304 := by
    intro i hi j hj he
    apply hApart _ (hContains i hi)
    rw [he]
    have hf : Finalize.frameBase s = initial.regValue .rsp -
        BitVec.ofNat 64 (mode.frameSize v keccak fullState + 304) := by
      simp only [Finalize.frameBase, hRsp, frameBase, BitVec.sub_sub, BitVec.ofNat_add,
        BitVec.add_assoc]
      rfl
    rw [hf]
    exact stack_sub_contains hCall.stackAvailable (by rw [Mode.stackBudget mode v keccak fullState]; omega) (by omega)
  have hOutputState : RangeApart out (v.digestBytes fullState)
      (frameBase initial v mode keccak fullState + BitVec.ofNat 64 offset) 201 := by
    intro i hi j hj he
    apply hApart _ (hContains i hi)
    rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact frameAddress_contains hCall.stackAvailable (by rw [Mode.stackBudget mode v keccak fullState]; omega) (by omega)
  have hPre := finalizeCallPre hCall hInv hOffset hAligned hRip hRsp hRdi hRsi
    hOut (fun i hi ↦ ⟨_, hMember, hContains i hi⟩) hOutputStack hOutputState
    hCursor hMetadata hLanes hTarget
  have hFinalize : ∃ t, Advances (returnBoundary initial)
      (if fullState then 6352 + 7 + Memcpy.memcpy200Steps out else Finalize.steps v false)
      s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      Finalize.CallResult v false state s t keccak fullState := by
    cases fullState with
    | false =>
      exact Finalize.call_advance hStride v false state (returnBoundary initial)
        (validInvocation_returnBoundary_bounds hInitial hCall).2 keccak
        s hInv.ready hInv.code hPre
    | true =>
      obtain ⟨rfl, rfl⟩ := hCall.fullState_valid rfl
      have hInside : s.regValue .rsp - (if false then 32 else 0) ≠
          (returnBoundary initial).rsp := by
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [hRsp, frameBase, BitVec.sub_sub, BitVec.sub_sub]
        apply stackSub_ne_returnBoundary
        cases mode <;> decide +kernel
      simpa only [hRsi, Bool.false_eq_true, ↓reduceIte] using
        Finalize.full_call_advance hStride false state (returnBoundary initial)
          (validInvocation_returnBoundary_bounds hInitial hCall).2
          s hInv.ready hInv.code hPre hInside
  obtain ⟨t, hRun, hReady, _, hResult⟩ := hFinalize
  have hInvT := hInv.of_callResult hCall hReady hResult.memory
    (finalizeWrites_cover hCall.stackAvailable hOffset hRsp hRdi hRsi
      (stack_mem_writeRegions initial v mode keccak fullState) hMember)
    hResult.grows hResult.rest
  have hSavedT := finalizeMemory_saved hCall.stackAvailable hOffset hRsp hRdi hRsi (Or.inl hApart)
    hResult.memory hSaved
  have hRspT : stackPtr t = frameBase initial v mode keccak fullState := by
    change t.regValue .rsp = _
    rw [hResult.stack, hRsp, BitVec.sub_add_cancel]
  obtain ⟨final, hReturnRun, hInvFinal, hMemory, hSavedFinal⟩ :=
    returnFromEpilogue hInitial hCall hInvT hSavedT (hResult.rip.trans hReturn) hRspT (by
      intro j hj
      exact (epiloguePopReg_read .plain false t j).trans
        ((hResult.saved _ (by clear hj; finite_cases j <;> decide)).trans
          ((epiloguePopReg_read .plain false s j).symm.trans (hPreserved j hj))))
  refine ⟨final, hRun.returns hReturnRun, hInvFinal, ?_, hSavedFinal, ?_⟩
  · intro i
    rw [hMemory, ← hRsi]
    exact hResult.output i
  · intro address ha
    rw [hMemory]
    exact hResult.memory address ha

def finalWrites (initial : RamState) (v : Variant) (mode : Mode) (out : BitVec 64)
    (keccak : Bool := false) (fullState : Bool := false) :
    Vector MemoryRegion 2 :=
  #v[Stack.region initial (mode.entry v keccak fullState).minStackBytes, ⟨out.toNat, (v.digestBytes fullState)⟩]

theorem atCall_returns [bindings : Bindings] (hStride : UnitStringStride bindings)
    {initial s : RamState} {v : Variant} {keccak fullState : Bool} {mode : Mode} {inputs : Array Input}
    {split offset : Nat} {state : Incremental.State} {out : BitVec 64}
    (hInitial : ReadyToStep initial)
    (hCall : ValidInvocation bindings v mode initial inputs split keccak fullState)
    (hMode : mode ≠ .plain) (hDigest : mode ≠ .digest)
    (hInv : Invariant initial v mode s keccak fullState) (hSaved : SavedFrame initial s mode fullState)
    (hOffset : offset + 201 ≤ (mode.frameSize v keccak fullState) - (8 * mode.pushCount fullState)) (hAligned : offset % 8 = 0)
    (hRip : s.RIP = callAddress mode v keccak fullState) (hRsp : stackPtr s = frameBase initial v mode keccak fullState)
    (hRdi : s.regValue .rdi = frameBase initial v mode keccak fullState + BitVec.ofNat 64 offset)
    (hRsi : s.regValue .rsi = out)
    (hOut : ValidOutput initial ⟨out.toNat, (v.digestBytes fullState)⟩)
    (hMember : (⟨out.toNat, (v.digestBytes fullState)⟩ : MemoryRegion) ∈ writeRegions initial v mode keccak fullState)
    (hApart : (⟨out.toNat, (v.digestBytes fullState)⟩ : MemoryRegion).Disjoint
      (Stack.region initial (mode.entry v keccak fullState).minStackBytes))
    (hCursor : state.cursor < v.rate)
    (hMetadata : (Operand.mem (frameBase initial v mode keccak fullState + BitVec.ofNat 64 offset + 200) :
      Operand 8).read s = BitVec.ofNat 8 state.cursor)
    (hLanes : Permutation.memoryLanes (frameBase initial v mode keccak fullState + BitVec.ofNat 64 offset) s =
      state.lanes) :
    ∃ final, Returns (returnBoundary initial) (1 + ((if fullState then 6352 + 7 + Memcpy.memcpy200Steps out else Finalize.steps v false) + 8)) s final ∧
      Invariant initial v mode final keccak fullState ∧
      (∀ i : Fin (v.digestBytes fullState), final.external[out + BitVec.ofNat 64 i.val]? =
        some (Finalize.digest v state keccak fullState)[i]) ∧
      CalleeSavedRegistersUnchanged initial final ∧
      MemoryWriteFrame s final (finalWrites initial v mode out keccak fullState) := by
  have hFrameBound : (mode.frameSize v keccak fullState) ≤ 1200 := by cases fullState <;> cases keccak <;> cases mode <;> cases v <;> decide +kernel
  obtain ⟨called, hCallRun, hInvCalled, hRipCalled, hRspCalled, hTop, hFrame, hEffect⟩ :=
    directCallAt (mode.frameSize v keccak fullState) (callAddress mode v keccak fullState) (callDisplacement mode v keccak fullState) hCall
      (by rw [Mode.stackBudget mode v keccak fullState]; omega) (by cases fullState <;> cases keccak <;> cases mode <;> cases v <;> decide +kernel)
      hInv hRip hRsp (callCode_subset mode v keccak fullState)
      (by rw [call_target mode v keccak fullState]; cases fullState <;> cases keccak <;> cases v <;> decide +kernel)
  have hRspCalled' : called.regValue .rsp = frameBase initial v mode keccak fullState - 8 := by
    rw [frameBase_sub_eight (keccak := keccak) (fullState := fullState)]
    exact hRspCalled
  have hRdiCalled : called.regValue .rdi = frameBase initial v mode keccak fullState + BitVec.ofNat 64 offset :=
    (hFrame.read (n := 64) (r := 7) (by simp)).trans hRdi
  have hRsiCalled : called.regValue .rsi = out :=
    (hFrame.read (n := 64) (r := 6) (by simp)).trans hRsi
  have hFrame' : AgreesExcept [.reg 4, .mem (frameBase initial v mode keccak fullState - 8) 8, .rip] s called := by
    simpa only [frameBase_sub_eight (keccak := keccak) (fullState := fullState)] using hFrame
  have hSavedCalled := hSaved.of_localFrame (mode := mode) hFrame' (by
    intro c hc address hCover
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact hCover.elim
    · obtain ⟨j, hj, he⟩ := hCover
      exact ⟨j, by omega, he⟩
    · exact hCover.elim)
  have hMetadataCalled : (Operand.mem (frameBase initial v mode keccak fullState + BitVec.ofNat 64 offset + 200) :
      Operand 8).read called = BitVec.ofNat 8 state.cursor := by
    have he := callRead_above hEffect (offset := offset + 200) (width := 8) (by omega)
    have haddr : stackPtr s + BitVec.ofNat 64 (offset + 200) =
        frameBase initial v mode keccak fullState + BitVec.ofNat 64 offset + 200 := by
      rw [hRsp, BitVec.ofNat_add, ← BitVec.add_assoc]
      rfl
    rw [haddr] at he
    exact he.trans hMetadata
  have hLanesCalled : Permutation.memoryLanes
      (frameBase initial v mode keccak fullState + BitVec.ofNat 64 offset) called = state.lanes := by
    rw [← hLanes]
    funext lane
    have he := callRead_above hEffect (offset := offset + 8 * lane.val) (width := 64)
      (by have := lane.isLt; omega)
    have haddr : stackPtr s + BitVec.ofNat 64 (offset + 8 * lane.val) =
        frameBase initial v mode keccak fullState + BitVec.ofNat 64 offset + BitVec.ofNat 64 (8 * lane.val) := by
      rw [hRsp, BitVec.ofNat_add, ← BitVec.add_assoc]
    rw [haddr] at he
    exact he
  obtain ⟨final, hReturn, hInvFinal, hOutput, hSavedFinal, hMemory⟩ :=
    called_returns hStride hInitial hCall hInvCalled hSavedCalled hOffset hAligned
      (by rw [call_target mode v keccak fullState] at hRipCalled; exact hRipCalled) hRspCalled' hRdiCalled hRsiCalled
      hOut hMember hApart hCursor hMetadataCalled hLanesCalled (hTop.trans (call_next mode v hMode hDigest keccak fullState)) (by
        cases fullState <;> cases mode <;> first
        | exact (hDigest rfl).elim
        | intro j hj; exact (hj j (by rfl)).elim)
  have hCount : mode.pushCount fullState + 2 = 8 := by
    cases fullState <;> cases mode <;> first | exact (hDigest rfl).elim | rfl
  rw [hCount] at hReturn
  have hStackMem : Stack.region initial (mode.entry v keccak fullState).minStackBytes ∈
      finalWrites initial v mode out keccak fullState := Vector.mem_iff_getElem.mpr ⟨0, by decide, rfl⟩
  have hOutMem : (⟨out.toNat, (v.digestBytes fullState)⟩ : MemoryRegion) ∈ finalWrites initial v mode out keccak fullState :=
    Vector.mem_iff_getElem.mpr ⟨1, by decide, rfl⟩
  have hMemoryCall : MemoryWriteFrame s called (finalWrites initial v mode out keccak fullState) := by
    apply hFrame.memoryWriteFrame
    intro c hc address hCover
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact hCover.elim
    · obtain ⟨i, hi, rfl⟩ := hCover
      exact ⟨_, hStackMem, stack_sub_contains hCall.stackAvailable
        (by rw [Mode.stackBudget mode v keccak fullState]; omega) (by omega)⟩
    · exact hCover.elim
  exact ⟨final, hCallRun.returns hReturn, hInvFinal, hOutput, hSavedFinal,
    memoryWriteFrame_trans hMemoryCall (memoryWriteFrame_mono hMemory
      (finalizeWrites_cover hCall.stackAvailable hOffset hRspCalled' hRdiCalled hRsiCalled
        hStackMem hOutMem))⟩

end Sha3.Proofs.Wrapper.Finish
