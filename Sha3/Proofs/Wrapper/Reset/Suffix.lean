import Sha3.Proofs.Wrapper.Reset.Selection
import Sha3.Proofs.Wrapper.Loop
import Sha3.Proofs.Wrapper.Setup.State

namespace Sha3.Proofs.Wrapper.Reset

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

def suffixKind (finalize : Bool) (finalizeMode : Mode := .finalizeReset) : Loop.Kind :=
  selectionKind finalize finalizeMode

theorem suffixKind_mode (finalize : Bool) (finalizeMode : Mode := .finalizeReset)
    (hMode : finalizeMode.hasBeforeOutput = true := by decide) :
    (suffixKind finalize finalizeMode).mode = mode finalize finalizeMode := by
  cases finalize <;> cases finalizeMode <;> first | rfl | contradiction

theorem suffixKind_start (v : Variant) (finalize : Bool)
    (keccak : Bool := false) (fullState : Bool := false)
    (finalizeMode : Mode := .finalizeReset) :
    (suffixKind finalize finalizeMode).start v keccak fullState =
      loopPC v finalize keccak fullState finalizeMode := rfl

theorem suffixKind_exit (v : Variant) (finalize : Bool)
    (keccak : Bool := false) (fullState : Bool := false)
    (finalizeMode : Mode := .finalizeReset) :
    (suffixKind finalize finalizeMode).exit v keccak fullState =
      finishPC v finalize keccak fullState finalizeMode := rfl

def suffixChanges (initial : RamState) (v : Variant) (finalize : Bool)
    (keccak : Bool := false) (fullState : Bool := false)
    (finalizeMode : Mode := .finalizeReset) : List Component :=
  selectionChanges finalize finalizeMode v fullState ++
    Loop.clobbers initial v (suffixKind finalize finalizeMode) keccak fullState

theorem suffix_with_update [bindings : Bindings] (v : Variant) (finalize : Bool)
    {keccak fullState : Bool} {finalizeMode : Mode}
    {initial s : RamState} {inputs : Array Input} {split : Nat}
    (hCall : ValidInvocation bindings v (mode finalize finalizeMode) initial inputs split keccak fullState)
    (outside : ¬ InProgram (returnBoundary initial).rip)
    (updateCorrect : Loop.UpdateCorrect v (returnBoundary initial))
    (inv : Invariant initial v (mode finalize finalizeMode) s keccak fullState)
    (initialized : Initialized initial v (mode finalize finalizeMode) s keccak fullState)
    (hip : s.RIP = comparePC v finalize keccak fullState finalizeMode)
    (hindex : (Operand.reg (indexReg finalize finalizeMode v fullState) : Operand 64).read s =
      BitVec.ofNat 64 (min split inputs.size))
    (hcount : (Operand.reg 15 : Operand 64).read s = BitVec.ofNat 64 inputs.size)
    (hpointers : s.regValue .r12 = initial.regValue .rdi)
    (hlengths : s.regValue .r14 = initial.regValue .rdx)
    (hMode : finalizeMode.hasBeforeOutput = true := by decide)
    (hbound : ((suffixKind finalize finalizeMode).boundOperand s v fullState).read s =
      BitVec.ofNat 64 inputs.size := by cases finalize <;> exact hcount) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧
      Invariant initial v (mode finalize finalizeMode) t keccak fullState ∧ SavedFrame initial t ∧
      stackPtr t = frameBase initial v (mode finalize finalizeMode) keccak fullState ∧
      Update.StateAt (statePointer initial v (mode finalize finalizeMode) keccak fullState)
        (Incremental.canonicalState Keccak.keccakLanes v.rate
          (message (inputs.extract split inputs.size))) t ∧
      t.RIP = finishPC v finalize keccak fullState finalizeMode ∧
      (Operand.reg (indexReg finalize finalizeMode v fullState) : Operand 64).read t = BitVec.ofNat 64 inputs.size ∧
      AgreesExcept (suffixChanges initial v finalize keccak fullState finalizeMode) s t ∧
      MemoryWriteFrame s t (Loop.writeRegions initial v (suffixKind finalize finalizeMode) keccak fullState) := by
  have hn : inputs.size < 2^64 := by
    rw [← (hCall.inputSlices (by cases finalize <;> cases finalizeMode <;> first | decide | contradiction)).countArgumentMatchesInputs]
    exact (initial.regValue .rsi).isLt
  have hi : min split inputs.size < 2^64 := Nat.lt_of_le_of_lt (Nat.min_le_right _ _) hn
  have sp : s.GPR[4] ≠ (returnBoundary initial).rsp := by
    change stackPtr s ≠ _
    rw [initialized.stack, frameBase]
    apply Finish.stackSub_ne_returnBoundary
    cases keccak <;> cases fullState <;> cases finalize <;> cases finalizeMode <;> cases v <;> decide +kernel
  obtain ⟨selectionFuel, selected, hselectRun, hselectInv, hselectRip, hselectPointer, hselectCursor, ha⟩ :=
    selection v finalize hCall inv hip sp hi hn hindex hcount hMode
  have hext : selected.external = s.external := ha.external (selectionChanges_noMem finalize finalizeMode v fullState)
  have hselectedSaved : SavedFrame initial selected := by
    have h := initialized.saved.of_external_eq hext
    cases finalize <;> cases finalizeMode <;> cases fullState <;>
      first | exact ⟨h.saved, h.returnSlot⟩ | contradiction
  have hselectedStack : stackPtr selected = frameBase initial v (mode finalize finalizeMode) keccak fullState :=
    (ha.read (n := 64) (r := 4)
      (by cases finalize <;> cases finalizeMode <;> cases v <;> cases fullState <;> simp [selectionChanges, stateReg, selectionKind, Loop.Kind.largeFollower, Loop.Kind.stateReg])).trans initialized.stack
  have hselectedIndex : (Operand.reg (indexReg finalize finalizeMode v fullState) : Operand 64).read selected =
      BitVec.ofNat 64 (min split inputs.size) :=
    (ha.read
      (by cases finalize <;> cases finalizeMode <;> cases v <;> cases fullState <;> simp [selectionChanges, stateReg, selectionKind, Loop.Kind.largeFollower, Loop.Kind.stateReg, indexReg, Loop.Kind.indexReg])).trans hindex
  have hselectedState : Update.StateAt (statePointer initial v (mode finalize finalizeMode) keccak fullState)
      Incremental.initial selected := initialized.stateAt.of_bytes_eq (by
    intro j hj
    rw [hext])
  have hselectionMemory : MemoryWriteFrame s selected
      (Loop.writeRegions initial v (suffixKind finalize finalizeMode) keccak fullState) := by
    intro address _
    rw [hext]
  by_cases hlt : min split inputs.size < inputs.size
  · have hsplit : split < inputs.size := by omega
    have hmin : min split inputs.size = split := Nat.min_eq_left (Nat.le_of_lt hsplit)
    have hloopState : Loop.State initial v (suffixKind finalize finalizeMode)
        inputs split inputs.size split selected keccak fullState := by
      refine ⟨?_, hselectedSaved, ?_, ?_, ?_⟩
      · simpa only [suffixKind_mode finalize finalizeMode hMode] using hselectInv
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · change stackPtr selected = _
          simpa only [suffixKind_mode finalize finalizeMode hMode] using hselectedStack
        · exact (ha.read (n := 64) (r := 12)
            (by cases finalize <;> cases finalizeMode <;> cases v <;> cases fullState <;> simp [selectionChanges, stateReg, selectionKind, Loop.Kind.largeFollower, Loop.Kind.stateReg])).trans hpointers
        · exact (ha.read (n := 64) (r := 14)
            (by cases finalize <;> cases finalizeMode <;> cases v <;> cases fullState <;> simp [selectionChanges, stateReg, selectionKind, Loop.Kind.largeFollower, Loop.Kind.stateReg])).trans hlengths
        · have hstackEq : selected.regValue .rsp = s.regValue .rsp :=
            ha.read (n := 64) (r := 4) (by
              cases finalize <;> cases finalizeMode <;> cases v <;> cases fullState <;>
                decide +kernel)
          have heq : ((suffixKind finalize finalizeMode).boundOperand selected v fullState).read selected =
              ((suffixKind finalize finalizeMode).boundOperand s v fullState).read s := by
            unfold Loop.Kind.boundOperand
            split
            · change memLoad selected.external (selected.regValue .rsp + _) 64 =
                memLoad s.external (s.regValue .rsp + _) 64
              rw [hstackEq, hext]
            · exact ha.read (by
                cases finalize <;> cases finalizeMode <;> cases v <;> cases fullState <;>
                  decide +kernel)
          exact heq.trans hbound
        · have hp := hselectPointer hlt
          change (Operand.reg (stateReg finalize finalizeMode v fullState) : Operand 64).read selected =
            stackPtr s + BitVec.ofNat 64 ((mode finalize finalizeMode).stateOffset v keccak fullState) at hp
          rw [initialized.stack] at hp
          change (Operand.reg ((suffixKind finalize finalizeMode).stateReg v fullState) : Operand 64).read selected = _ at hp
          simpa only [suffixKind_mode finalize finalizeMode hMode, statePointer] using hp
        · intro r hr
          have hh := hselectCursor hlt r hr
          change _ = stackPtr s + _ at hh
          rw [initialized.stack] at hh
          simpa only [suffixKind_mode finalize finalizeMode hMode, statePointer,
            BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using hh
      · rw [hmin] at hselectedIndex
        exact hselectedIndex
      · simpa only [suffixKind_mode finalize finalizeMode hMode, Loop.absorbed,
          Array.extract_empty_of_stop_le_start (Nat.le_refl split),
          Incremental.message_empty, Incremental.canonicalState_empty] using hselectedState
    have hloopCall : ValidInvocation bindings v (suffixKind finalize finalizeMode).mode
        initial inputs split keccak fullState := by simpa only [suffixKind_mode finalize finalizeMode hMode] using hCall
    have hloopRip : selected.RIP = Loop.position (suffixKind finalize finalizeMode) v split inputs.size keccak fullState := by
      simpa only [Loop.position, hsplit, ite_true, suffixKind_start v finalize keccak fullState finalizeMode, hlt] using hselectRip
    obtain ⟨loopFuel, t, hloopRun, ht, htRip, htAgrees, htMemory⟩ :=
      Loop.advance_with_update hloopCall outside updateCorrect (Nat.le_refl split)
        (Nat.le_of_lt hsplit) (Nat.le_refl inputs.size) hloopState hloopRip
    refine ⟨selectionFuel + loopFuel, t, hselectRun.trans hloopRun, ?_, ht.saved,
      ?_, ?_, htRip.trans (suffixKind_exit v finalize keccak fullState finalizeMode), ?_, ha.trans htAgrees,
      memoryWriteFrame_trans hselectionMemory htMemory⟩
    · simpa only [suffixKind_mode finalize finalizeMode hMode] using ht.invariant
    · change t.regValue .rsp = _
      simpa only [suffixKind_mode finalize finalizeMode hMode] using ht.registers.stack
    · simpa only [suffixKind_mode finalize finalizeMode hMode, Loop.absorbed] using ht.state
    · have hh := ht.index
      exact hh
  · have hsizeSplit : inputs.size ≤ split := by omega
    have hmin : min split inputs.size = inputs.size := Nat.min_eq_right hsizeSplit
    refine ⟨selectionFuel, selected, hselectRun, hselectInv, hselectedSaved,
      hselectedStack, ?_, ?_, ?_, ?_, hselectionMemory⟩
    · simpa only [Array.extract_empty_of_size_le_start hsizeSplit,
        Incremental.message_empty, Incremental.canonicalState_empty] using hselectedState
    · simpa only [hlt, ite_false] using hselectRip
    · simpa only [hmin] using hselectedIndex
    · exact ha.mono (fun c hc ↦ List.mem_append_left _ hc)

theorem suffix_outputSlot {initial s t : RamState} {v : Variant} {finalize : Bool} {keccak fullState : Bool} {finalizeMode : Mode}
    (ha : AgreesExcept (Reset.suffixChanges initial v finalize keccak fullState finalizeMode) s t)
    (hMode : finalizeMode.hasBeforeOutput = true := by decide) :
    (Operand.mem (outputSlot initial v (Reset.mode finalize finalizeMode) keccak fullState) : Operand 64).read t =
      (Operand.mem (outputSlot initial v (Reset.mode finalize finalizeMode) keccak fullState) : Operand 64).read s := by
  apply memLoad_congr
  intro j hj
  change (t.external[outputSlot initial v (Reset.mode finalize finalizeMode) keccak fullState + BitVec.ofNat 64 j]?).getD 0 =
    (s.external[outputSlot initial v (Reset.mode finalize finalizeMode) keccak fullState + BitVec.ofNat 64 j]?).getD 0
  rw [ha.byte]
  intro c hc hcover
  rcases List.mem_append.mp hc with hc | hc
  · exact (Reset.selectionChanges_noMem finalize finalizeMode v fullState) c hc _ hcover
  · have hslot : ((Reset.suffixKind finalize finalizeMode).mode.outputSlotOffset v keccak fullState) + 8 ≤
        ((Reset.suffixKind finalize finalizeMode).mode.stateOffset v keccak fullState) := by cases keccak <;> cases fullState <;> cases finalize <;> cases finalizeMode <;> cases v <;> decide
    have hh := Loop.slot_avoids (initial := initial) (keccak := keccak) (fullState := fullState) hslot j hj c hc
    rw [Reset.suffixKind_mode finalize finalizeMode hMode] at hh
    exact hh hcover

end Sha3.Proofs.Wrapper.Reset
