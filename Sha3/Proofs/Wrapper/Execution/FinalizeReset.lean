import Sha3.Proofs.Wrapper.Execution.Reset
import Sha3.Proofs.Wrapper.Reset.Finalize

namespace Sha3.Proofs.Wrapper

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

set_option maxHeartbeats 1600000 in
theorem finalize_reset_after_first_with_update [bindings : Bindings]
    (hstride : UnitStringStride bindings) {initial s : RamState} {v : Variant}
    {inputs : Array Input} {split : Nat} {keccak fullState : Bool} {mode : Mode} {hNotDigest : mode ≠ .digest}
    (hInitial : ReadyToStep initial)
    (hCall : ValidInvocation (keccak := keccak) (fullState := fullState) bindings v mode initial inputs split)
    (updateCorrect : Loop.UpdateCorrect v (returnBoundary initial))
    (h : Setup.FirstResult (keccak := keccak) (fullState := fullState) initial v mode inputs split s (hMode := hNotDigest))
    (hMode : mode.hasBeforeOutput = true := by decide) :
    ∃ fuel final, Returns (returnBoundary initial) fuel s final ∧
      ExecutionResult (keccak := keccak) (fullState := fullState) v mode initial inputs split final := by
  have hFirstCount : Setup.firstCount mode inputs split = min split inputs.size := by
    cases mode <;> first | contradiction | rfl
  have hAfter : afterInputs mode inputs split = inputs.extract split inputs.size := by
    cases mode <;> first | contradiction | rfl
  have hOutputSlot : (Operand.mem (outputSlot initial v mode keccak fullState) : Operand 64).read s =
      initial.regValue .r9 := by
    cases mode <;> first | contradiction | exact h.output.1
  have hBeforeInitial : if Setup.firstCount mode inputs split = 0 then
      (Reset.beforeOutputOperand initial v mode keccak fullState).read s = initial.regValue .rcx
      else (Reset.beforeOutputSource initial v mode keccak fullState).read s = initial.regValue .rcx := by
    cases mode <;> first | contradiction | exact h.output.2
  have hprepared : ∃ fuel prepared, Advances (returnBoundary initial) fuel s prepared ∧
      Invariant (keccak := keccak) (fullState := fullState) initial v mode prepared ∧ SavedFrame initial prepared mode fullState ∧
      stackPtr prepared = frameBase (keccak := keccak) (fullState := fullState) initial v mode ∧
      Update.StateAt (statePointer (keccak := keccak) (fullState := fullState) initial v mode)
        (Loop.absorbed v inputs 0 (Setup.firstCount mode inputs split)) prepared ∧
      prepared.RIP = Reset.preparePC v true keccak fullState mode ∧ (Reset.beforeOutputOperand initial v mode keccak fullState).read prepared = initial.regValue .rcx ∧
      prepared.regValue .r15 = initial.regValue .rsi ∧
      AgreesExcept Reset.restoreChanges s prepared := by
    by_cases hzero : Setup.firstCount mode inputs split = 0
    · refine ⟨0, s, (advances_zero _ _ _).2 rfl, h.invariant, h.saved, h.stack,
        h.state, ?_, ?_, h.countAtZero hzero, AgreesExcept.refl _ _⟩
      · apply h.rip.trans
        cases mode <;> cases fullState <;> cases v <;> cases keccak
        all_goals first | contradiction | (simp only [Setup.firstExit, hzero, ite_true]; rfl)
      · simpa only [hzero, ite_true] using hBeforeInitial
    · obtain ⟨hpFuel, prepared, hpRun, hpInv, hpRip, hpOutput, hpCount, hpMemory, hpFrame⟩ :=
        Reset.restore_before_output v hCall h.invariant (by
          apply h.rip.trans
          cases mode <;> cases fullState <;> cases v <;> cases keccak
          all_goals first | contradiction | (simp only [Setup.firstExit, hzero, ite_false]; rfl)) h.stack hMode
      refine ⟨hpFuel, prepared, hpRun, hpInv, h.saved.of_external_eq hpMemory,
        (hpFrame.read (n := 64) (r := 4) (by decide)).trans h.stack,
        h.state.of_bytes_eq (by intro i hi; rw [hpMemory]), hpRip, ?_, ?_, hpFrame⟩
      · exact hpOutput.trans (by simpa only [hzero, ite_false] using hBeforeInitial)
      · have hh := h.count
        cases mode <;> cases fullState <;> cases v <;>
          first | contradiction | exact hpCount.trans hh
  obtain ⟨prepareFuel, prepared, hpRun, hpInv, hpSaved, hpStack, hpState, hpRip, hpOutput, hpCount, hpFrame⟩ :=
    hprepared
  obtain ⟨finalizeFuel, cleared, hcRun, hc⟩ := Reset.finalize_steps hstride v hInitial hCall hpInv hpSaved
    hpRip hpStack hpOutput hpState (Loop.absorbed_cursor_lt _ _ _ _) hMode
  have hBound : (Operand.reg (Reset.indexReg true mode v fullState) : Operand 64).read s =
      BitVec.ofNat 64 (min split inputs.size) := by
    have hb := h.bound (by intro he; subst mode; cases hMode)
    cases mode <;> cases fullState <;> cases v <;> first | contradiction | exact hb
  have hcIndex : (Operand.reg (Reset.indexReg true mode v fullState) : Operand 64).read cleared =
      BitVec.ofNat 64 (min split inputs.size) :=
    hc.index.trans ((hpFrame.read (n := 64) (r := Reset.indexReg true mode v fullState)
      (by cases mode <;> cases fullState <;> cases v <;> decide)).trans hBound)
  have hcCount : (Operand.reg 15 : Operand 64).read cleared = BitVec.ofNat 64 inputs.size := by
    have hh : (Operand.reg 15 : Operand 64).read cleared = initial.regValue .rsi :=
      (hc.saved .r15 (by split <;> simp)).trans hpCount
    rw [hh, ← (hCall.inputSlices hNotDigest).countArgumentMatchesInputs, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hcPointers : cleared.regValue .r12 = initial.regValue .rdi :=
    (hc.saved .r12 (by split <;> simp)).trans ((hpFrame.read (n := 64) (r := 12) (by decide)).trans h.pointers)
  have hcLengths : cleared.regValue .r14 = initial.regValue .rdx :=
    (hc.saved .r14 (by split <;> simp)).trans ((hpFrame.read (n := 64) (r := 14) (by decide)).trans h.lengths)
  have hpMemory := hpFrame.external (by simp [Reset.restoreChanges, Component.Covers])
  have hCountWord : initial.regValue .rsi = BitVec.ofNat 64 inputs.size := by
    rw [← (hCall.inputSlices hNotDigest).countArgumentMatchesInputs,
      BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hcSlot (offset : Nat) (hb : offset + 8 ≤ 24) :
      (Operand.mem (frameBase initial v mode keccak fullState + BitVec.ofNat 64 offset) : Operand 64).read cleared =
      (Operand.mem (frameBase initial v mode keccak fullState + BitVec.ofNat 64 offset) : Operand 64).read s := by
    rw [hc.lowSlots offset hb]
    change memLoad prepared.external _ 64 = memLoad s.external _ 64
    rw [hpMemory]
  have hcBound : ((Reset.suffixKind true mode).boundOperand cleared v fullState).read cleared =
      BitVec.ofNat 64 inputs.size := by
    have hsp : (Operand.reg 4 : Operand 64).read cleared = frameBase initial v mode keccak fullState :=
      hc.initialized.stack
    cases mode <;> cases fullState <;> cases v
    all_goals try contradiction
    all_goals try exact hcCount
    all_goals simp only [Reset.suffixKind, ite_true,
      Loop.Kind.boundOperand, Loop.Kind.memoryBound, Loop.Kind.largeFollower, Loop.Kind.boundReg,
      Bool.false_or, Bool.true_or, beq_self_eq_true,
      Bool.false_eq_true, ite_false, hsp]
    all_goals first
      | exact (hcSlot 0 (by decide)).trans (h.count.trans hCountWord)
      | exact (hcSlot 8 (by decide)).trans (h.count.trans hCountWord)
  have hcOutput : (Operand.mem (outputSlot (keccak := keccak) (fullState := fullState) initial v mode) : Operand 64).read cleared =
      initial.regValue .r9 := by
    rw [hc.outputSlot]
    change memLoad prepared.external _ 64 = _
    rw [hpMemory]
    exact hOutputSlot
  have hExtract : inputs.extract 0 (min split inputs.size) = inputs.extract 0 split := by
    apply Array.ext
    · simp only [Array.size_extract, Nat.sub_zero, Nat.min_assoc, Nat.min_self]
    · intro i hi hj
      simp only [Array.getElem_extract]
  have hcBefore : readOutput (mode.entry v keccak fullState) initial cleared =
      .ok (expectedBeforeDigest (keccak := keccak) (fullState := fullState) v inputs split mode) := by
    apply beforeOutput_of_canonical_at_address (v := v) (mode := mode)
      (inputs := inputs) (split := split) (keccak := keccak) (fullState := fullState)
    simpa only [Loop.absorbed, hFirstCount, hExtract] using hc.output
  obtain ⟨fuel, t, htRun, htInv, htSaved, htStack, htState, htRip, _, htFrame, htMemory⟩ :=
    Reset.suffix_with_update v true (finalizeMode := mode) hCall
      (validInvocation_returnBoundary_bounds hInitial hCall).2 updateCorrect hc.invariant hc.initialized
      hc.rip hcIndex hcCount hcPointers hcLengths hMode (hbound := hcBound)
  have htOutput : (Finish.outputOperand (keccak := keccak) (fullState := fullState) initial v mode).read t =
      outputAddress initial mode := by
    have hh := (Reset.suffix_outputSlot htFrame hMode).trans hcOutput
    cases mode <;> first | contradiction |
      simpa only [Finish.outputOperand, outputAddress, Reset.mode, ite_true] using hh
  have htBefore : readOutput (mode.entry v keccak fullState) initial t =
      .ok (expectedBeforeDigest (keccak := keccak) (fullState := fullState) v inputs split mode) := by
    rw [readOutput, readOutput_of_memoryWriteFrame (hCall.beforeOutputWritable hMode).2.1 rfl htMemory ?_]
    · exact hcBefore
    · intro region hr address hOutput hRegion
      apply before_stack_disjoint hCall hMode address hOutput
      have hk : (Reset.suffixKind true mode).mode = mode := by
        simpa only [Reset.mode, ite_true] using Reset.suffixKind_mode true mode hMode
      have hStack : Stack.Valid initial ((Reset.suffixKind true mode).mode.entry v keccak fullState).minStackBytes := by
        simpa only [hk] using hCall.stackAvailable
      simpa only [hk] using Loop.writeRegions_contains_stack (v := v) hStack hr hRegion
  obtain ⟨_, final, hReturn, hResult⟩ := finish_execution hstride hInitial hCall htInv (by cases mode <;> cases fullState <;> first | contradiction | exact ⟨htSaved.saved, htSaved.returnSlot⟩)
    (htRip.trans (by cases mode <;> cases keccak <;> cases fullState <;> cases v <;> first | contradiction | rfl)) htStack htOutput (by simpa only [hAfter, Reset.mode, ite_true] using htState) (fun _ ↦ htBefore)
      (fun he ↦ (hNotDigest he).elim) (fun he ↦ (hNotDigest he).elim)
      (fun he ↦ (hNotDigest he).elim)
  exact ⟨_, final, ((hpRun.trans hcRun).trans htRun).returns hReturn, hResult⟩

end Sha3.Proofs.Wrapper
