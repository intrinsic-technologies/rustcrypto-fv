import Sha3.Proofs.Wrapper.Finish.FinalizeCall
import Sha3.Proofs.Finalize
import Sha3.Proofs.Wrapper.Finish.Plain.Code
import Sha3.Proofs.Wrapper.Setup.Initialize
import Sha3.Proofs.Wrapper.Finish.Arguments

namespace Sha3.Proofs.Wrapper.Finish.Plain

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

theorem digest_region_contains {initial : RamState} {v : Variant} {mode : Mode} {keccak fullState : Bool}
    {offset : Nat}
    (hStack : Stack.Valid initial (mode.entry v keccak fullState).minStackBytes)
    (hd : offset + v.digestBytes fullState ≤ mode.frameSize v keccak fullState + 8)
    {address : Nat}
    (ha : (MemoryRegion.mk
      (frameBase initial v mode keccak fullState + BitVec.ofNat 64 offset).toNat
      (v.digestBytes fullState)).Contains address) :
    (Stack.region initial (mode.entry v keccak fullState).minStackBytes).Contains address := by
  have hb : mode.frameSize v keccak fullState ≤ (mode.entry v keccak fullState).minStackBytes := by
    rw [Mode.stackBudget mode v keccak fullState]; omega
  obtain ⟨hl, hu⟩ := frameBase_bounds hStack hb
  simp only [MemoryRegion.Contains] at ha
  rw [frameAddress_toNat hStack hb (by omega)] at ha
  change _ ≤ address ∧ address < _
  constructor <;> omega

theorem digest_output_valid {initial : RamState} {v : Variant} {mode : Mode} {keccak fullState : Bool}
    {offset : Nat}
    (hStack : Stack.Valid initial (mode.entry v keccak fullState).minStackBytes)
    (hd : offset + v.digestBytes fullState ≤ mode.frameSize v keccak fullState + 8) :
    ValidOutput initial
      ⟨(frameBase initial v mode keccak fullState + BitVec.ofNat 64 offset).toNat,
        (v.digestBytes fullState)⟩ := by
  have hb : mode.frameSize v keccak fullState ≤ (mode.entry v keccak fullState).minStackBytes := by
    rw [Mode.stackBudget mode v keccak fullState]; omega
  have hn : (frameBase initial v mode keccak fullState).toNat =
      (initial.regValue .rsp).toNat - mode.frameSize v keccak fullState :=
    stack_sub_toNat hStack.2.2.1 hb
  have hs := hStack.2.2.1
  change (mode.entry v keccak fullState).minStackBytes ≤ (initial.regValue .rsp).toNat at hs
  rw [Mode.stackBudget mode v keccak fullState] at hs
  refine ⟨?_, ?_, ?_⟩
  · change (frameBase initial v mode keccak fullState + BitVec.ofNat 64 offset).toNat ≠ 0
    rw [frameAddress_toNat hStack hb (by omega), hn]
    omega
  · obtain ⟨_, hu⟩ := frameBase_bounds hStack hb
    have hbound : (Stack.region initial (mode.entry v keccak fullState).minStackBytes).start +
        (Stack.region initial (mode.entry v keccak fullState).minStackBytes).size < 2^32 := hStack.1
    change (frameBase initial v mode keccak fullState + BitVec.ofNat 64 offset).toNat +
      (v.digestBytes fullState) < 2^32
    rw [frameAddress_toNat hStack hb (by omega)]
    omega
  · intro address ha
    exact hStack.2.1 address (digest_region_contains hStack hd ha)

theorem finalize_output_stack {initial s : RamState} {v : Variant} {keccak : Bool}
    {mode : Mode} (hMode : mode = .plain ∨ mode = .digest)
    (hRsp : s.regValue .rsp = frameBase initial v mode keccak - 8) :
    RangeApart (frameBase initial v mode keccak + BitVec.ofNat 64 (digestOffset mode))
      v.digestBytes (Finalize.frameBase s) 304 := by
  have hf : Finalize.frameBase s = frameBase initial v mode keccak - 304 := by
    simp only [Finalize.frameBase, hRsp, BitVec.sub_sub]; rfl
  rw [hf]
  have hd := v.digestBytes_le
  have hr := v.rate_le
  have ho : digestOffset mode ≤ 8 := by rcases hMode with rfl | rfl <;> decide +kernel
  simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.ofNat_eq_ofNat,
    BitVec.add_zero, BitVec.sub_add_cancel] using
    (RangeApart.offsets (frameBase initial v mode keccak - 304)
      (a := 304 + digestOffset mode) (b := 0) (len := v.digestBytes) (count := 304)
      (by omega) (by decide) (.inr (by omega)))

theorem finalize_output_state (initial : RamState) (v : Variant) (keccak : Bool := false)
    (mode : Mode := .plain) (hMode : mode = .plain ∨ mode = .digest := by decide) :
    RangeApart (frameBase initial v mode keccak + BitVec.ofNat 64 (digestOffset mode))
      v.digestBytes (statePointer initial v mode keccak) 201 := by
  have hd : digestOffset mode + v.digestBytes ≤ mode.stateOffset v keccak := by
    rcases hMode with rfl | rfl <;> cases keccak <;> cases v <;> decide +kernel
  have hs : mode.stateOffset v keccak + 201 ≤ 1000 := by
    rcases hMode with rfl | rfl <;> cases keccak <;> cases v <;> decide +kernel
  exact RangeApart.offsets (frameBase initial v mode keccak)
    (a := digestOffset mode) (b := mode.stateOffset v keccak)
    (len := v.digestBytes) (count := 201) (by omega) (by omega) (.inl hd)

theorem digest_below_saved {initial : RamState} {v : Variant} {keccak fullState : Bool}
    {mode : Mode} {offset : Nat}
    (hStack : Stack.Valid initial (mode.entry v keccak fullState).minStackBytes)
    (hd : offset + v.digestBytes fullState + 8 * mode.pushCount fullState ≤
      mode.frameSize v keccak fullState) :
    (frameBase initial v mode keccak fullState + BitVec.ofNat 64 offset).toNat +
      (v.digestBytes fullState) ≤ (initial.regValue .rsp).toNat - 8 * (mode.pushCount fullState) := by
  have hb : mode.frameSize v keccak fullState ≤ (mode.entry v keccak fullState).minStackBytes := by
    rw [Mode.stackBudget mode v keccak fullState]; omega
  have hn : (frameBase initial v mode keccak fullState).toNat =
      (initial.regValue .rsp).toNat - mode.frameSize v keccak fullState :=
    stack_sub_toNat hStack.2.2.1 hb
  have hs := hStack.2.2.1
  change (mode.entry v keccak fullState).minStackBytes ≤ (initial.regValue .rsp).toNat at hs
  rw [frameAddress_toNat hStack hb (by omega), hn]
  omega

theorem finalize_slot_read {initial s t : RamState} {v : Variant} {keccak fullState : Bool} {mode : Mode} {offset : Nat}
    (hMode : mode = .plain ∨ mode = .digest)
    (hStack : Stack.Valid initial (mode.entry v keccak fullState).minStackBytes)
    (hRsp : s.regValue .rsp = frameBase initial v mode keccak fullState - 8)
    (hRdi : s.regValue .rdi = statePointer initial v mode keccak fullState)
    (hRsi : s.regValue .rsi = frameBase initial v mode keccak fullState + BitVec.ofNat 64 offset)
    (hMemory : MemoryWriteFrame s t (Finalize.writeRegions v s fullState))
    (hSaved : CalleeSavedRegistersUnchanged s t)
    (hBound : offset + v.digestBytes fullState ≤ mode.frameSize v keccak fullState + 8)
    (hApart : mode = .plain → mode.outputSlotOffset v keccak fullState + 8 ≤ offset ∨
      offset + v.digestBytes fullState ≤ mode.outputSlotOffset v keccak fullState) :
    (outputOperand initial v mode keccak fullState).read t = (outputOperand initial v mode keccak fullState).read s := by
  rcases hMode with rfl | rfl
  · have hApart := hApart rfl
    have hb : Mode.plain.frameSize v keccak fullState ≤ (Mode.plain.entry v keccak fullState).minStackBytes := by
      rw [Mode.stackBudget .plain v keccak fullState]; omega
    have hbase : (frameBase initial v .plain keccak fullState).toNat =
        (initial.regValue .rsp).toNat - Mode.plain.frameSize v keccak fullState :=
      stack_sub_toNat hStack.2.2.1 hb
    have hsp : (s.regValue .rsp).toNat =
        (initial.regValue .rsp).toNat - (Mode.plain.frameSize v keccak fullState + 8) := by
      rw [hRsp, frameBase, BitVec.sub_sub,
        show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, ← BitVec.ofNat_add]
      exact stack_sub_toNat hStack.2.2.1 (by rw [Mode.stackBudget .plain v keccak fullState]; omega)
    have hstate : (s.regValue .rdi).toNat =
        (frameBase initial v .plain keccak fullState).toNat + Mode.plain.stateOffset v keccak fullState := by
      rw [hRdi, statePointer, frameAddress_toNat hStack hb (by cases fullState <;> cases keccak <;> cases v <;> decide)]
    have htemp : (s.regValue .rsi).toNat =
        (frameBase initial v .plain keccak fullState).toNat + offset := by
      rw [hRsi, frameAddress_toNat hStack hb (by omega)]
    have hslot : Mode.plain.outputSlotOffset v keccak fullState + 8 ≤ Mode.plain.stateOffset v keccak fullState := by
      cases fullState <;> cases keccak <;> cases v <;> decide +kernel
    have hframe : Mode.plain.stateOffset v keccak fullState ≤ Mode.plain.frameSize v keccak fullState := by
      cases fullState <;> cases keccak <;> cases v <;> decide +kernel
    have hsize := hStack.2.2.1
    change (Mode.plain.entry v keccak fullState).minStackBytes ≤ (initial.regValue .rsp).toNat at hsize
    rw [Mode.stackBudget .plain v keccak fullState] at hsize
    apply memLoad_congr
    intro j hj
    apply congrArg (fun x : Option UInt8 ↦ x.getD 0)
    change t.external[outputSlot initial v .plain keccak fullState + BitVec.ofNat 64 j]? = s.external[_]?
    apply hMemory
    intro region hr ha
    have haddr : (outputSlot initial v .plain keccak fullState + BitVec.ofNat 64 j).toNat =
        (frameBase initial v .plain keccak fullState).toNat + (Mode.plain.outputSlotOffset v keccak fullState + j) := by
      rw [outputSlot, BitVec.add_assoc, ← BitVec.ofNat_add,
        frameAddress_toNat hStack hb (by omega)]
    obtain ⟨i, hi, rfl⟩ := Vector.mem_iff_getElem.mp hr
    have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hi' with rfl | rfl | rfl
    · change (Stack.region s 296).Contains _ at ha
      simp only [Stack.region, Stack.returnAddressBytes, MemoryRegion.Contains, hsp, haddr] at ha
      omega
    · change (MemoryRegion.mk (s.regValue .rdi).toNat 201).Contains _ at ha
      simp only [MemoryRegion.Contains, hstate, haddr] at ha
      omega
    · change (MemoryRegion.mk (s.regValue .rsi).toNat (v.digestBytes fullState)).Contains _ at ha
      simp only [MemoryRegion.Contains, htemp, haddr] at ha
      omega
  · exact hSaved .rbx (by simp)

theorem called_advance [bindings : Bindings] (hStride : UnitStringStride bindings)
    {initial s : RamState} {v : Variant} {keccak : Bool} {mode : Mode}
    (hMode : mode = .plain ∨ mode = .digest) {inputs : Array Input} {split : Nat}
    {state : Incremental.State} {out : BitVec 64}
    (hInitial : ReadyToStep initial)
    (hCall : ValidInvocation bindings v mode initial inputs split keccak)
    (hInv : Invariant initial v mode s keccak) (hSaved : SavedFrame initial s mode)
    (hRip : s.RIP = Finalize.entryAddress v false keccak)
    (hRsp : s.regValue .rsp = frameBase initial v mode keccak - 8)
    (hRdi : s.regValue .rdi = statePointer initial v mode keccak)
    (hRsi : s.regValue .rsi = frameBase initial v mode keccak + BitVec.ofNat 64 (digestOffset mode))
    (hOutput : (outputOperand initial v mode keccak).read s = out)
    (hCursor : state.cursor < v.rate)
    (hMetadata : (Operand.mem (statePointer initial v mode keccak + 200) : Operand 8).read s =
      BitVec.ofNat 8 state.cursor)
    (hLanes : Permutation.memoryLanes (statePointer initial v mode keccak) s = state.lanes)
    (hReturn : stackTop s = callAddress mode v keccak + 5) :
    ∃ t, Advances (returnBoundary initial) (Finalize.steps v false) s t ∧
      Invariant initial v mode t keccak ∧ SavedFrame initial t mode ∧
      t.RIP = (callAddress mode v keccak + (5 : BitVec 64)) ∧ stackPtr t = frameBase initial v mode keccak ∧
      (outputOperand initial v mode keccak).read t = out ∧
      (∀ i : Fin v.digestBytes, t.external[frameBase initial v mode keccak + BitVec.ofNat 64 (digestOffset mode) + BitVec.ofNat 64 i.val]? =
        some (Finalize.digest v state keccak)[i]) ∧
      MemoryWriteFrame s t #v[Stack.region initial (mode.entry v keccak).minStackBytes] ∧
      CalleeSavedRegistersUnchanged s t := by
  have hOffset : mode.stateOffset v keccak + 201 ≤ mode.frameSize v keccak - 8 * mode.pushCount := by
    rcases hMode with rfl | rfl <;> cases keccak <;> cases v <;> decide +kernel
  have hAligned : mode.stateOffset v keccak % 8 = 0 := by rcases hMode with rfl | rfl <;> cases keccak <;> cases v <;> decide +kernel
  have hTarget : InProgram (stackTop s) := by
    rw [hReturn]
    refine ⟨if v = .sha224 then 0x8b else 0x48, ?_⟩
    apply imageSections_mem_toCodeMap_of_fetchByte
    rcases hMode with rfl | rfl <;> cases keccak <;> cases v <;> decide +kernel
  have hContains : ∀ i < v.digestBytes, ∃ region ∈ writeRegions initial v mode keccak,
      region.Contains (frameBase initial v mode keccak + BitVec.ofNat 64 (digestOffset mode) + BitVec.ofNat 64 i).toNat := by
    intro i hi
    refine ⟨_, stack_mem_writeRegions initial v mode keccak, ?_⟩
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    apply frameAddress_contains hCall.stackAvailable (by rw [Mode.stackBudget mode v keccak]; omega)
    have hd : digestOffset mode + v.digestBytes ≤ mode.frameSize v keccak := by rcases hMode with rfl | rfl <;> cases keccak <;> cases v <;> decide +kernel
    omega
  have hDigestBound : digestOffset mode + v.digestBytes ≤ mode.frameSize v keccak + 8 := by
    rcases hMode with rfl | rfl <;> cases keccak <;> cases v <;> decide +kernel
  have hPre := finalizeCallPre hCall hInv hOffset hAligned hRip hRsp hRdi hRsi
    (digest_output_valid hCall.stackAvailable hDigestBound) hContains (finalize_output_stack hMode hRsp)
    (finalize_output_state initial v keccak mode hMode) hCursor hMetadata hLanes hTarget
  obtain ⟨t, hRun, hReady, _, hResult⟩ :=
    Finalize.call_advance (keccak := keccak) hStride v false state (returnBoundary initial)
      (validInvocation_returnBoundary_bounds hInitial hCall).2 s hInv.ready hInv.code hPre
  have hMemory : MemoryWriteFrame s t
      #v[Stack.region initial (mode.entry v keccak).minStackBytes] := by
    apply memoryWriteFrame_mono hResult.memory
    intro region hr address ha
    have hc := finalizeWrites_cover hCall.stackAvailable hOffset hRsp hRdi hRsi
      (regions := #v[Stack.region initial (mode.entry v keccak).minStackBytes,
        ⟨(frameBase initial v mode keccak + BitVec.ofNat 64 (digestOffset mode)).toNat, v.digestBytes⟩])
      (Vector.mem_iff_getElem.mpr ⟨0, by decide, rfl⟩)
      (Vector.mem_iff_getElem.mpr ⟨1, by decide, rfl⟩) region hr address ha
    obtain ⟨target, ht, hc⟩ := hc
    refine ⟨_, Vector.mem_iff_getElem.mpr ⟨0, by decide, rfl⟩, ?_⟩
    obtain ⟨j, hj, rfl⟩ := Vector.mem_iff_getElem.mp ht
    have hj' : j = 0 ∨ j = 1 := by omega
    rcases hj' with rfl | rfl
    · exact hc
    · exact digest_region_contains hCall.stackAvailable hDigestBound hc
  have hInvT := hInv.of_callResult hCall hReady hMemory (by
    intro region hr address ha
    have he : region = Stack.region initial (mode.entry v keccak).minStackBytes := by simpa using hr
    exact ⟨_, stack_mem_writeRegions initial v mode keccak, he ▸ ha⟩) hResult.grows hResult.rest
  have hSavedT := finalizeMemory_saved hCall.stackAvailable hOffset hRsp hRdi hRsi
    (Or.inr (digest_below_saved hCall.stackAvailable (by
      rcases hMode with rfl | rfl <;> cases keccak <;> cases v <;> decide +kernel))) hResult.memory hSaved
  refine ⟨t, hRun, hInvT, hSavedT, hResult.rip.trans hReturn, ?_, ?_, ?_, hMemory, hResult.saved⟩
  · change t.regValue .rsp = _
    rw [hResult.stack, hRsp, BitVec.sub_add_cancel]
  · exact (finalize_slot_read hMode hCall.stackAvailable hRsp hRdi hRsi hResult.memory hResult.saved
      (by rcases hMode with rfl | rfl <;> cases keccak <;> cases v <;> decide +kernel)
      (by intro hm; subst mode; right; cases keccak <;> cases v <;> decide +kernel)).trans hOutput
  · simpa only [hRsi] using hResult.output


theorem atCall_advance [bindings : Bindings] (hStride : UnitStringStride bindings)
    {initial s : RamState} {v : Variant} {keccak : Bool} {mode : Mode}
    (hMode : mode = .plain ∨ mode = .digest) {inputs : Array Input} {split : Nat}
    {state : Incremental.State} {out : BitVec 64}
    (hInitial : ReadyToStep initial)
    (hCall : ValidInvocation bindings v mode initial inputs split keccak)
    (hInv : Invariant initial v mode s keccak) (hSaved : SavedFrame initial s mode)
    (hRip : s.RIP = callAddress mode v keccak) (hRsp : stackPtr s = frameBase initial v mode keccak)
    (hRdi : s.regValue .rdi = statePointer initial v mode keccak)
    (hRsi : s.regValue .rsi = frameBase initial v mode keccak + BitVec.ofNat 64 (digestOffset mode))
    (hOutput : (outputOperand initial v mode keccak).read s = out)
    (hCursor : state.cursor < v.rate)
    (hMetadata : (Operand.mem (statePointer initial v mode keccak + 200) : Operand 8).read s =
      BitVec.ofNat 8 state.cursor)
    (hLanes : Permutation.memoryLanes (statePointer initial v mode keccak) s = state.lanes) :
    ∃ t, Advances (returnBoundary initial) (1 + Finalize.steps v false) s t ∧
      Invariant initial v mode t keccak ∧ SavedFrame initial t mode ∧
      t.RIP = (callAddress mode v keccak + (5 : BitVec 64)) ∧ stackPtr t = frameBase initial v mode keccak ∧
      (outputOperand initial v mode keccak).read t = out ∧
      (∀ i : Fin v.digestBytes, t.external[frameBase initial v mode keccak + BitVec.ofNat 64 (digestOffset mode) + BitVec.ofNat 64 i.val]? =
        some (Finalize.digest v state keccak)[i]) ∧
      MemoryWriteFrame s t #v[Stack.region initial (mode.entry v keccak).minStackBytes] ∧
      CalleeSavedRegistersUnchanged s t := by
  have hOffsetBound : mode.stateOffset v keccak ≤ 136 := by rcases hMode with rfl | rfl <;> cases keccak <;> cases v <;> decide +kernel
  have hFrameBound : (mode.frameSize v keccak) ≤ 488 := by rcases hMode with rfl | rfl <;> cases keccak <;> cases v <;> decide +kernel
  obtain ⟨called, hCallRun, hInvCalled, hRipCalled, hRspCalled, hTop, hFrame, hEffect⟩ :=
    directCallAt (mode.frameSize v keccak) (callAddress mode v keccak) (callDisplacement mode v keccak) hCall
      (by rw [Mode.stackBudget mode v keccak]; omega) (by rcases hMode with rfl | rfl <;> cases keccak <;> cases v <;> decide +kernel)
      hInv hRip hRsp (callCode_subset mode v keccak)
      (by rw [call_target mode v keccak]; rcases hMode with rfl | rfl <;> cases keccak <;> cases v <;> decide +kernel)
  have hRspCalled' : called.regValue .rsp = frameBase initial v mode keccak - 8 := by
    rw [frameBase_sub_eight initial v mode keccak]
    exact hRspCalled
  have hRdiCalled : called.regValue .rdi = frameBase initial v mode keccak + BitVec.ofNat 64 (mode.stateOffset v keccak) :=
    (hFrame.read (n := 64) (r := 7) (by simp)).trans hRdi
  have hRsiCalled : called.regValue .rsi = frameBase initial v mode keccak + BitVec.ofNat 64 (digestOffset mode) :=
    (hFrame.read (n := 64) (r := 6) (by simp)).trans hRsi
  have hFrame' : AgreesExcept [.reg 4, .mem (frameBase initial v mode keccak - 8) 8, .rip] s called := by
    simpa only [frameBase_sub_eight initial v mode keccak] using hFrame
  have hSavedCalled := hSaved.of_localFrame (mode := mode) (keccak := keccak) hFrame' (by
    intro c hc address hCover
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact hCover.elim
    · obtain ⟨j, hj, he⟩ := hCover
      exact ⟨j, by rcases hMode with rfl | rfl <;> cases keccak <;> cases v <;> simp only [Mode.frameSize, Mode.pushCount, Bool.false_eq_true, ↓reduceIte] <;> omega, he⟩
    · exact hCover.elim)
  have hMetadataCalled : (Operand.mem (frameBase initial v mode keccak + BitVec.ofNat 64 (mode.stateOffset v keccak) + 200) :
      Operand 8).read called = BitVec.ofNat 8 state.cursor := by
    have he := callRead_above hEffect (offset := (mode.stateOffset v keccak) + 200) (width := 8) (by omega)
    have haddr : stackPtr s + BitVec.ofNat 64 ((mode.stateOffset v keccak) + 200) =
        frameBase initial v mode keccak + BitVec.ofNat 64 (mode.stateOffset v keccak) + 200 := by
      rw [hRsp, BitVec.ofNat_add, ← BitVec.add_assoc]
      rfl
    rw [haddr] at he
    exact he.trans hMetadata
  have hLanesCalled : Permutation.memoryLanes
      (frameBase initial v mode keccak + BitVec.ofNat 64 (mode.stateOffset v keccak)) called = state.lanes := by
    rw [← hLanes]
    funext lane
    have he := callRead_above hEffect (offset := (mode.stateOffset v keccak) + 8 * lane.val) (width := 64)
      (by have := lane.isLt; omega)
    have haddr : stackPtr s + BitVec.ofNat 64 ((mode.stateOffset v keccak) + 8 * lane.val) =
        frameBase initial v mode keccak + BitVec.ofNat 64 (mode.stateOffset v keccak) + BitVec.ofNat 64 (8 * lane.val) := by
      rw [hRsp, BitVec.ofNat_add, ← BitVec.add_assoc]
    rw [haddr] at he
    exact he
  have hOutputCalled : (outputOperand initial v mode keccak).read called = out := by
    rcases hMode with rfl | rfl
    · have he := callRead_above hEffect (offset := Mode.plain.outputSlotOffset v keccak)
        (width := 64) (by cases keccak <;> cases v <;> decide +kernel)
      rw [hRsp] at he
      exact he.trans hOutput
    · exact (hFrame.read (n := 64) (r := 3) (by simp)).trans hOutput
  obtain ⟨t, hRun, hInvT, hSavedT, hRipT, hRspT, hOutT, hBytes, hMemory, hPreserved⟩ :=
    called_advance hStride hMode hInitial hCall hInvCalled hSavedCalled
      (by rw [call_target mode v keccak] at hRipCalled; exact hRipCalled) hRspCalled'
      hRdiCalled hRsiCalled hOutputCalled hCursor hMetadataCalled hLanesCalled hTop
  have hMemoryCall : MemoryWriteFrame s called
      #v[Stack.region initial (mode.entry v keccak).minStackBytes] := by
    apply hFrame.memoryWriteFrame
    intro c hc address hCover
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact hCover.elim
    · obtain ⟨i, hi, rfl⟩ := hCover
      exact ⟨_, Vector.mem_iff_getElem.mpr ⟨0, by decide, rfl⟩,
        stack_sub_contains hCall.stackAvailable (by rw [Mode.stackBudget mode v keccak]; omega) (by omega)⟩
    · exact hCover.elim
  refine ⟨t, hCallRun.trans hRun, hInvT, hSavedT, hRipT, hRspT, hOutT, hBytes,
    memoryWriteFrame_trans hMemoryCall hMemory, ?_⟩
  have hCallSaved := calleeSavedRegistersUnchanged_of_agreesExcept hFrame (by
    intro register hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, Component.reg.injEq] <;>
      decide +kernel)
  intro register hr
  exact (hPreserved register hr).trans (hCallSaved register hr)

end Sha3.Proofs.Wrapper.Finish.Plain
