import Sha3.Proofs.Wrapper.Reset.Finalize.Prepare
import Sha3.Proofs.Wrapper.Finish.Plain.Call
import Sha3.Proofs.Wrapper.Regions

namespace Sha3.Proofs.Wrapper.Reset

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

def finalizeWriteRegions (initial : RamState) (v : Variant)
    (keccak : Bool := false) (fullState : Bool := false)
    (finalizeMode : Mode := .finalizeReset) : Vector MemoryRegion 2 :=
  #v[outputRegion (finalizeMode.entry v keccak fullState) initial,
    Stack.region initial (finalizeMode.entry v keccak fullState).minStackBytes]

theorem beforeOutput_region (initial : RamState) (v : Variant)
    (keccak : Bool := false) (fullState : Bool := false)
    (finalizeMode : Mode := .finalizeReset) :
    outputRegion (finalizeMode.entry v keccak fullState) initial =
      ⟨(initial.regValue .rcx).toNat, v.digestBytes fullState⟩ := by
  simp only [outputRegion, registerRegion, Mode.entry_digestBytes]

theorem beforeOutput_mem (initial : RamState) (v : Variant)
    (keccak : Bool := false) (fullState : Bool := false)
    (finalizeMode : Mode := .finalizeReset)
    (hMode : finalizeMode.hasBeforeOutput = true := by decide) :
    (⟨(initial.regValue .rcx).toNat, v.digestBytes fullState⟩ : MemoryRegion) ∈
      writeRegions initial v finalizeMode keccak fullState := by
  rw [← beforeOutput_region initial v keccak fullState finalizeMode]
  cases finalizeMode <;> try cases hMode
  all_goals exact Vector.mem_iff_getElem.mpr ⟨0, by decide, rfl⟩

theorem beforeOutput_valid {bindings : Bindings} {initial : RamState} {v : Variant}
    {keccak fullState : Bool} {finalizeMode : Mode} {inputs : Array Input} {split : Nat}
    (hCall : ValidInvocation bindings v finalizeMode initial inputs split keccak fullState)
    (hMode : finalizeMode.hasBeforeOutput = true := by decide) :
    ValidOutput initial ⟨(initial.regValue .rcx).toNat, v.digestBytes fullState⟩ := by
  rw [← beforeOutput_region initial v keccak fullState finalizeMode]
  exact hCall.beforeOutputWritable hMode

theorem beforeOutput_stack {bindings : Bindings} {initial : RamState} {v : Variant}
    {keccak fullState : Bool} {finalizeMode : Mode} {inputs : Array Input} {split : Nat}
    (hCall : ValidInvocation bindings v finalizeMode initial inputs split keccak fullState)
    (hMode : finalizeMode.hasBeforeOutput = true := by decide) :
    (⟨(initial.regValue .rcx).toNat, v.digestBytes fullState⟩ : MemoryRegion).Disjoint
      (Stack.region initial (finalizeMode.entry v keccak fullState).minStackBytes) := by
  rw [← beforeOutput_region initial v keccak fullState finalizeMode]
  exact before_stack_disjoint hCall hMode

theorem finalizeMemory_afterSlot [bindings : Bindings] {initial s t : RamState}
    {v : Variant} {keccak fullState : Bool} {finalizeMode : Mode}
    {state : Incremental.State} {inputs : Array Input} {split : Nat}
    (h : FinalizeResetEntry initial v state s keccak fullState finalizeMode)
    (hCall : ValidInvocation bindings v finalizeMode initial inputs split keccak fullState)
    (hMemory : MemoryWriteFrame s t (Finalize.writeRegions v s fullState))
    (offset : Nat := finalizeMode.outputSlotOffset v keccak fullState)
    (hOffset : offset + 8 ≤ finalizeMode.stateOffset v keccak fullState := by
      simp [Mode.outputSlotOffset, Mode.stateOffset])
    (hTemp : (finalizeMode = .finalizeFixedReset ∨ finalizeMode = .digestFinalizeReset) →
      offset + 8 ≤ Output.tempOffset v fullState := by
      simp [Mode.outputSlotOffset, Output.tempOffset]) :
    (Operand.mem (frameBase initial v finalizeMode keccak fullState + BitVec.ofNat 64 offset) : Operand 64).read t =
      (Operand.mem (frameBase initial v finalizeMode keccak fullState + BitVec.ofNat 64 offset) : Operand 64).read s := by
  have hBudget : finalizeMode.frameSize v keccak fullState ≤
      (finalizeMode.entry v keccak fullState).minStackBytes := by
    rw [Mode.stackBudget finalizeMode v keccak fullState]; omega
  have hUnder : finalizeMode.frameSize v keccak fullState + 464 ≤ (initial.regValue .rsp).toNat := by
    simpa only [Stack.NoUnderflow, Mode.stackBudget] using hCall.stackAvailable.2.2.1
  have hBase : (frameBase initial v finalizeMode keccak fullState).toNat =
      (initial.regValue .rsp).toNat - finalizeMode.frameSize v keccak fullState :=
    stack_sub_toNat hCall.stackAvailable.2.2.1 hBudget
  have hSp : (s.regValue .rsp).toNat = (initial.regValue .rsp).toNat -
      (finalizeMode.frameSize v keccak fullState + 8) := by
    rw [h.stack, frameBase_sub_eight (keccak := keccak) (fullState := fullState)]
    exact stack_sub_toNat hCall.stackAvailable.2.2.1
      (by rw [Mode.stackBudget finalizeMode v keccak fullState]; omega)
  have hState : (s.regValue .rdi).toNat = (frameBase initial v finalizeMode keccak fullState).toNat +
      finalizeMode.stateOffset v keccak fullState := by
    rw [h.pointer, statePointer, frameAddress_toNat hCall.stackAvailable hBudget
      (by cases keccak <;> cases finalizeMode <;> cases fullState <;> cases v <;> decide)]
  have hm := h.modeValid
  have hb : finalizeMode.stateOffset v keccak fullState ≤ finalizeMode.frameSize v keccak fullState := by
    cases keccak <;> cases finalizeMode <;> cases fullState <;> cases v <;> decide
  apply memLoad_congr
  intro j hj
  apply congrArg (fun x : Option UInt8 ↦ x.getD 0)
  apply hMemory
  intro region hr ha
  have hAddress : (frameBase initial v finalizeMode keccak fullState + BitVec.ofNat 64 offset + BitVec.ofNat 64 j).toNat =
      (frameBase initial v finalizeMode keccak fullState).toNat +
        (offset + j) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add,
      frameAddress_toNat hCall.stackAvailable hBudget (by omega)]
  obtain ⟨i, hi, rfl⟩ := Vector.mem_iff_getElem.mp hr
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi' with rfl | rfl | rfl
  · change (Stack.region s 296).Contains _ at ha
    simp only [Stack.region, Stack.returnAddressBytes, MemoryRegion.Contains, hSp,
      hAddress, hBase] at ha
    omega
  · change (⟨(s.regValue .rdi).toNat, 201⟩ : MemoryRegion).Contains _ at ha
    simp only [MemoryRegion.Contains, hState, hAddress] at ha
    omega
  · change (⟨(s.regValue .rsi).toNat, v.digestBytes fullState⟩ : MemoryRegion).Contains _ at ha
    rw [h.output] at ha
    by_cases hc : finalizeMode = .finalizeFixedReset ∨ finalizeMode = .digestFinalizeReset
    · have hp : finalizeOutputPointer initial v finalizeMode keccak fullState =
          Output.tempPointer initial v finalizeMode keccak fullState := by
        rcases hc with rfl | rfl <;> rfl
      have ht := hTemp hc
      have htemp := (Output.temp_bounds v finalizeMode keccak fullState hc).1
      rw [hp, Output.tempPointer, frameAddress_toNat hCall.stackAvailable hBudget (by omega)] at ha
      simp only [MemoryRegion.Contains, hAddress] at ha
      omega
    · have hp : finalizeOutputPointer initial v finalizeMode keccak fullState = initial.regValue .rcx := by
        cases finalizeMode <;> first | rfl | exact (hc (Or.inl rfl)).elim | exact (hc (Or.inr rfl)).elim
      rw [hp] at ha
      apply beforeOutput_stack hCall hm _ ha
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact frameAddress_contains hCall.stackAvailable hBudget (by omega)

theorem finalizeOutput_valid {bindings : Bindings} {initial : RamState} {v : Variant}
    {keccak fullState : Bool} {finalizeMode : Mode} {inputs : Array Input} {split : Nat}
    (hCall : ValidInvocation bindings v finalizeMode initial inputs split keccak fullState)
    (hMode : finalizeMode.hasBeforeOutput = true) :
    ValidOutput initial ⟨(finalizeOutputPointer initial v finalizeMode keccak fullState).toNat,
      v.digestBytes fullState⟩ := by
  by_cases hc : finalizeMode = .finalizeFixedReset ∨ finalizeMode = .digestFinalizeReset
  · have hb := (Output.temp_bounds v finalizeMode keccak fullState hc).1
    have hv := Finish.Plain.digest_output_valid (offset := Output.tempOffset v fullState)
      hCall.stackAvailable (by omega)
    rcases hc with rfl | rfl <;> exact hv
  · have hp : finalizeOutputPointer initial v finalizeMode keccak fullState = initial.regValue .rcx := by
      cases finalizeMode <;> first | rfl | exact (hc (Or.inl rfl)).elim | exact (hc (Or.inr rfl)).elim
    rw [hp]
    exact beforeOutput_valid hCall hMode

theorem finalizeOutput_cover {bindings : Bindings} {initial : RamState} {v : Variant}
    {keccak fullState : Bool} {finalizeMode : Mode} {inputs : Array Input} {split : Nat}
    (hCall : ValidInvocation bindings v finalizeMode initial inputs split keccak fullState)
    {address : Nat}
    (ha : (⟨(finalizeOutputPointer initial v finalizeMode keccak fullState).toNat,
      v.digestBytes fullState⟩ : MemoryRegion).Contains address) :
    ∃ region ∈ finalizeWriteRegions initial v keccak fullState finalizeMode, region.Contains address := by
  by_cases hc : finalizeMode = .finalizeFixedReset ∨ finalizeMode = .digestFinalizeReset
  · refine ⟨_, Vector.mem_iff_getElem.mpr ⟨1, by decide, rfl⟩, ?_⟩
    have hb := (Output.temp_bounds v finalizeMode keccak fullState hc).1
    apply Finish.Plain.digest_region_contains (offset := Output.tempOffset v fullState)
      hCall.stackAvailable (by omega)
    rcases hc with rfl | rfl <;> exact ha
  · refine ⟨_, Vector.mem_iff_getElem.mpr ⟨0, by decide, rfl⟩, ?_⟩
    change (outputRegion (finalizeMode.entry v keccak fullState) initial).Contains address
    rw [beforeOutput_region initial v keccak fullState finalizeMode]
    have hp : finalizeOutputPointer initial v finalizeMode keccak fullState = initial.regValue .rcx := by
      cases finalizeMode <;> first | rfl | exact (hc (Or.inl rfl)).elim | exact (hc (Or.inr rfl)).elim
    simpa only [hp] using ha

theorem finalizeWriteRegions_subset (initial : RamState) (v : Variant)
    (keccak fullState : Bool) (finalizeMode : Mode)
    (hMode : finalizeMode.hasBeforeOutput = true) :
    ∀ region ∈ finalizeWriteRegions initial v keccak fullState finalizeMode,
      region ∈ writeRegions initial v finalizeMode keccak fullState := by
  intro region hr
  obtain ⟨i, hi, rfl⟩ := Vector.mem_iff_getElem.mp hr
  have hi' : i = 0 ∨ i = 1 := by omega
  rcases hi' with rfl | rfl
  · rw [show (finalizeWriteRegions initial v keccak fullState finalizeMode)[0] =
      outputRegion (finalizeMode.entry v keccak fullState) initial by rfl, beforeOutput_region initial v keccak fullState finalizeMode]
    exact beforeOutput_mem initial v keccak fullState finalizeMode hMode
  · exact stack_mem_writeRegions initial v finalizeMode keccak fullState

theorem FinalizeResetEntry.pre [bindings : Bindings] {initial s : RamState} {v : Variant}
    {keccak fullState : Bool} {finalizeMode : Mode}
    {state : Incremental.State} {inputs : Array Input} {split : Nat}
    (h : FinalizeResetEntry initial v state s keccak fullState finalizeMode)
    (hCall : ValidInvocation bindings v finalizeMode initial inputs split keccak fullState)
    (hCursor : state.cursor < v.rate) :
    Finalize.CallPre (returnBoundary initial) v true state s keccak fullState := by
  have hm := h.modeValid
  have hb : finalizeMode.frameSize v keccak fullState ≤ (finalizeMode.entry v keccak fullState).minStackBytes := by
    rw [Mode.stackBudget finalizeMode v keccak fullState]; omega
  have hOff : finalizeMode.stateOffset v keccak fullState + 201 ≤
      finalizeMode.frameSize v keccak fullState - 8 * finalizeMode.pushCount fullState := by
    cases keccak <;> cases finalizeMode <;> cases fullState <;> cases v <;> decide
  have hAligned : finalizeMode.stateOffset v keccak fullState % 8 = 0 := by
    cases keccak <;> cases finalizeMode <;> cases fullState <;> cases v <;> decide
  have hValid := finalizeOutput_valid hCall hm
  have hContains : ∀ i < v.digestBytes fullState,
      (⟨(finalizeOutputPointer initial v finalizeMode keccak fullState).toNat,
        v.digestBytes fullState⟩ : MemoryRegion).Contains
        (finalizeOutputPointer initial v finalizeMode keccak fullState + BitVec.ofNat 64 i).toNat :=
    fun _ hi ↦ Finalize.region_contains_byte (Nat.le_of_lt hValid.2.1) hi
  have hApart : RangeApart (finalizeOutputPointer initial v finalizeMode keccak fullState)
      (v.digestBytes fullState) (Finalize.frameBase s) 304 ∧
      RangeApart (finalizeOutputPointer initial v finalizeMode keccak fullState)
        (v.digestBytes fullState) (statePointer initial v finalizeMode keccak fullState) 201 := by
    by_cases hc : finalizeMode = .finalizeFixedReset ∨ finalizeMode = .digestFinalizeReset
    · have hp : finalizeOutputPointer initial v finalizeMode keccak fullState =
          Output.tempPointer initial v finalizeMode keccak fullState := by
        rcases hc with rfl | rfl <;> rfl
      rw [hp, Output.tempPointer]
      have ht := Output.temp_bounds v finalizeMode keccak fullState hc
      have hf : finalizeMode.frameSize v keccak fullState ≤ 1200 := by
        cases keccak <;> cases finalizeMode <;> cases fullState <;> cases v <;> decide
      constructor
      · have hs : Finalize.frameBase s = frameBase initial v finalizeMode keccak fullState - 304 := by
          simp only [Finalize.frameBase, h.stack, BitVec.sub_sub]; rfl
        rw [hs]
        have he : frameBase initial v finalizeMode keccak fullState + BitVec.ofNat 64 (Output.tempOffset v fullState) =
            (frameBase initial v finalizeMode keccak fullState - 304) + BitVec.ofNat 64 (304 + Output.tempOffset v fullState) := by
          rw [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, ← BitVec.add_assoc, BitVec.sub_add_cancel]
        rw [he]
        simpa only [BitVec.add_zero] using RangeApart.offsets
          (frameBase initial v finalizeMode keccak fullState - 304)
          (a := 304 + Output.tempOffset v fullState) (len := v.digestBytes fullState)
          (b := 0) (count := 304) (by omega) (by decide) (.inr (by omega))
      · exact RangeApart.offsets (frameBase initial v finalizeMode keccak fullState)
          (a := Output.tempOffset v fullState) (len := v.digestBytes fullState)
          (b := finalizeMode.stateOffset v keccak fullState) (count := 201)
          (by omega) (by omega) ht.2
    · have hp : finalizeOutputPointer initial v finalizeMode keccak fullState = initial.regValue .rcx := by
        cases finalizeMode <;> first | rfl | exact (hc (Or.inl rfl)).elim | exact (hc (Or.inr rfl)).elim
      constructor
      · intro i hi j hj he
        apply beforeOutput_stack hCall hm _ (by simpa only [hp] using hContains i hi)
        rw [← hp, he]
        have hf : Finalize.frameBase s = initial.regValue .rsp -
            BitVec.ofNat 64 (finalizeMode.frameSize v keccak fullState + 304) := by
          simp only [Finalize.frameBase, h.stack, frameBase, BitVec.sub_sub, BitVec.ofNat_add, BitVec.add_assoc]; rfl
        rw [hf]
        exact stack_sub_contains hCall.stackAvailable
          (by rw [Mode.stackBudget finalizeMode v keccak fullState]; omega) (by omega)
      · intro i hi j hj he
        apply beforeOutput_stack hCall hm _ (by simpa only [hp] using hContains i hi)
        rw [← hp, he, statePointer, BitVec.add_assoc, ← BitVec.ofNat_add]
        exact frameAddress_contains hCall.stackAvailable hb (by omega)
  apply Finish.finalizeCallPre hCall h.invariant hOff hAligned
    h.rip h.stack h.pointer h.output hValid ?_ hApart.1 hApart.2 hCursor
    (metadata_of_stateAt h.state) h.state.lanes ?_
  · intro i hi
    obtain ⟨region, hr, ha⟩ := finalizeOutput_cover hCall (hContains i hi)
    exact ⟨region, finalizeWriteRegions_subset initial v keccak fullState finalizeMode hm region hr, ha⟩
  · rw [h.target]
    exact finalize_return_inProgram v keccak fullState finalizeMode hm

theorem finalizeOutput_saved {bindings : Bindings} {initial : RamState} {v : Variant}
    {keccak fullState : Bool} {finalizeMode : Mode} {inputs : Array Input} {split : Nat}
    (hCall : ValidInvocation bindings v finalizeMode initial inputs split keccak fullState)
    (hMode : finalizeMode.hasBeforeOutput = true) :
    (⟨(finalizeOutputPointer initial v finalizeMode keccak fullState).toNat,
      v.digestBytes fullState⟩ : MemoryRegion).Disjoint
        (Stack.region initial (finalizeMode.entry v keccak fullState).minStackBytes) ∨
    (finalizeOutputPointer initial v finalizeMode keccak fullState).toNat + v.digestBytes fullState ≤
      (initial.regValue .rsp).toNat - 8 * finalizeMode.pushCount fullState := by
  by_cases hc : finalizeMode = .finalizeFixedReset ∨ finalizeMode = .digestFinalizeReset
  · right
    have ht := (Output.temp_bounds v finalizeMode keccak fullState hc).1
    have hs : 48 ≤ finalizeMode.frameSize v keccak fullState := by
      cases keccak <;> cases finalizeMode <;> cases fullState <;> cases v <;> decide
    have hpush : 8 * finalizeMode.pushCount fullState = 48 := by
      rcases hc with rfl | rfl <;> rfl
    have hv := Finish.Plain.digest_below_saved (offset := Output.tempOffset v fullState)
      hCall.stackAvailable (by rw [hpush]; omega)
    rcases hc with rfl | rfl <;> exact hv
  · left
    have hp : finalizeOutputPointer initial v finalizeMode keccak fullState = initial.regValue .rcx := by
      cases finalizeMode <;> first | rfl | exact (hc (Or.inl rfl)).elim | exact (hc (Or.inr rfl)).elim
    rw [hp]
    exact beforeOutput_stack hCall hMode

theorem finalizeMemory_before [bindings : Bindings] {initial s t : RamState} {v : Variant}
    {keccak fullState : Bool} {finalizeMode : Mode}
    {state : Incremental.State} {inputs : Array Input} {split : Nat}
    (h : FinalizeResetEntry initial v state s keccak fullState finalizeMode)
    (hCall : ValidInvocation bindings v finalizeMode initial inputs split keccak fullState)
    (hMemory : MemoryWriteFrame s t (Finalize.writeRegions v s fullState)) :
    MemoryWriteFrame s t (finalizeWriteRegions initial v keccak fullState finalizeMode) := by
  have hcover := Finish.finalizeWrites_cover (regions :=
      #v[⟨(finalizeOutputPointer initial v finalizeMode keccak fullState).toNat, v.digestBytes fullState⟩,
        Stack.region initial (finalizeMode.entry v keccak fullState).minStackBytes])
    hCall.stackAvailable
    (show finalizeMode.stateOffset v keccak fullState + 201 ≤
        finalizeMode.frameSize v keccak fullState - 8 * finalizeMode.pushCount fullState by
      cases keccak <;> cases finalizeMode <;> cases fullState <;> cases v <;> decide)
    h.stack h.pointer h.output
    (Vector.mem_iff_getElem.mpr ⟨1, by decide, rfl⟩)
    (Vector.mem_iff_getElem.mpr ⟨0, by decide, rfl⟩)
  apply memoryWriteFrame_mono hMemory
  intro region hr address ha
  obtain ⟨target, ht, hc⟩ := hcover region hr address ha
  obtain ⟨i, hi, rfl⟩ := Vector.mem_iff_getElem.mp ht
  have hi' : i = 0 ∨ i = 1 := by omega
  rcases hi' with rfl | rfl
  · exact finalizeOutput_cover hCall hc
  · exact ⟨_, Vector.mem_iff_getElem.mpr ⟨1, by decide, rfl⟩, hc⟩

theorem enter_finalize_memory {initial s t : RamState} {v : Variant}
    {keccak fullState : Bool} {finalizeMode : Mode}
    (hStack : Stack.Valid initial (finalizeMode.entry v keccak fullState).minStackBytes)
    (ha : AgreesExcept (finalizePrepareChanges initial v finalizeMode keccak fullState ++
      [.reg 4, .mem (frameBase initial v finalizeMode keccak fullState - 8) 8, .rip]) s t) :
    MemoryWriteFrame s t (finalizeWriteRegions initial v keccak fullState finalizeMode) := by
  apply ha.memoryWriteFrame
  intro c hc address hcover
  simp only [List.mem_append] at hc
  rcases hc with hc | hc
  · by_cases hm : finalizeMode = .finalizeFixedReset ∨ finalizeMode = .digestFinalizeReset
    · simp only [finalizePrepareChanges, ite_eq_left hm, List.mem_append] at hc
      rcases hc with hc | hc
      · refine ⟨Stack.region initial (finalizeMode.entry v keccak fullState).minStackBytes,
          Vector.mem_iff_getElem.mpr ⟨1, by decide, rfl⟩, ?_⟩
        cases fullState with
        | false =>
          obtain ⟨i, hi, rfl⟩ := Output.Zero.prepareChanges_cover hc hcover
          have ht := (Output.temp_bounds v finalizeMode keccak false hm).1
          exact frameAddress_contains hStack
            (by rw [Mode.stackBudget finalizeMode v keccak false]; omega) (by omega)
        | true =>
          obtain ⟨i, hi, he⟩ := Output.Zero.fullChanges_local initial finalizeMode hm c hc address hcover
          have hf : frameBase initial .sha256 finalizeMode true true =
              frameBase initial v finalizeMode keccak true := by
            cases finalizeMode <;> cases v <;> rfl
          have hsize : finalizeMode.frameSize .sha256 true true = finalizeMode.frameSize v keccak true := by
            cases finalizeMode <;> cases v <;> rfl
          rw [he, hf, frameBase_sub_eight (keccak := keccak) (fullState := true)]
          rw [hsize] at hi
          exact stack_sub_contains hStack
            (by rw [Mode.stackBudget finalizeMode v keccak true]; omega) (by omega)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl <;> exact hcover.elim
    · simp only [finalizePrepareChanges, ite_eq_right hm] at hc
      exact (prepareChanges_noMem c hc address hcover).elim
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact hcover.elim
    · obtain ⟨j, hj, rfl⟩ := hcover
      refine ⟨Stack.region initial (finalizeMode.entry v keccak fullState).minStackBytes,
        Vector.mem_iff_getElem.mpr ⟨1, by decide, rfl⟩, ?_⟩
      rw [frameBase_sub_eight (keccak := keccak) (fullState := fullState)]
      exact stack_sub_contains hStack (by
        rw [Mode.stackBudget finalizeMode v keccak fullState]; omega) (by omega)
    · exact hcover.elim

end Sha3.Proofs.Wrapper.Reset
