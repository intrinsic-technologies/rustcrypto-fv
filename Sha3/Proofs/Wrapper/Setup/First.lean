import Sha3.Proofs.Wrapper.Setup.Entry
import Sha3.Proofs.Wrapper.Setup.State
import Sha3.Proofs.Wrapper.Setup.Selection
import Sha3.Proofs.Wrapper.Loop
import Sha3.Proofs.Wrapper.Finish.Call
import Sha3.Proofs.Wrapper.Loop.Memory
import Sha3.Proofs.Update.Frame
import Sha3.Proofs.Wrapper.Finish.Code

namespace Sha3.Proofs.Wrapper.Setup

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

def firstCount (mode : Mode) (inputs : Array Input) (split : Nat) : Nat :=
  match mode with
  | .plain | .digest => inputs.size
  | _ => min split inputs.size

def firstExit (v : Variant) (mode : Mode) (inputs : Array Input) (split : Nat)
    (keccak : Bool := false) (fullState : Bool := false)
    (hMode : mode ≠ .digest := by decide) : BitVec 64 :=
  match mode with
  | .plain => (mode.entry v keccak fullState).entryAddress + 0x6f
  | .reset => (mode.entry v keccak fullState).entryAddress + 0x84
  | .finalizeReset | .digestFinalizeIntoReset =>
      (mode.entry v keccak fullState).entryAddress +
        if firstCount mode inputs split = 0 then 0x99 else 0x94
  | .finalizeFixedReset | .digestFinalizeReset =>
      if firstCount mode inputs split = 0 then
        Selection.skipAddress v true keccak fullState (mode == .digestFinalizeReset) true
      else (firstKind mode).exit v keccak fullState
  | .digest => False.elim (hMode rfl)

structure FirstResult [Bindings] (initial : RamState) (v : Variant) (mode : Mode)
    (inputs : Array Input) (split : Nat) (s : RamState)
    (keccak : Bool := false) (fullState : Bool := false)
    (hMode : mode ≠ .digest := by decide) : Prop where
  invariant : Invariant initial v mode s keccak fullState
  saved : SavedFrame initial s mode fullState
  stack : stackPtr s = frameBase initial v mode keccak fullState
  pointers : s.regValue .r12 = initial.regValue .rdi
  lengths : s.regValue .r14 = initial.regValue .rdx
  count : (if (firstKind mode).largeFollower v fullState then
      (Operand.mem (frameBase initial v mode keccak fullState + if fullState then 8 else 0) : Operand 64)
      else Operand.reg 15).read s = initial.regValue .rsi
  bound : mode ≠ .plain → (Operand.reg ((firstKind mode).boundReg v fullState) : Operand 64).read s =
    BitVec.ofNat 64 (firstCount mode inputs split)
  state : Update.StateAt (statePointer initial v mode keccak fullState)
    (Loop.absorbed v inputs 0 (firstCount mode inputs split)) s
  rip : s.RIP = firstExit v mode inputs split keccak fullState hMode
  output : match mode with
    | .plain | .reset => (Operand.mem (outputSlot initial v mode keccak fullState) : Operand 64).read s =
        initial.regValue .rcx
    | .finalizeReset | .digestFinalizeIntoReset =>
        (Operand.mem (outputSlot initial v mode keccak fullState) : Operand 64).read s = initial.regValue .r9 ∧
        (if firstCount mode inputs split = 0 then s.regValue .rbp = initial.regValue .rcx
        else (Operand.mem (frameBase initial v mode keccak fullState + 8) : Operand 64).read s = initial.regValue .rcx)
    | .finalizeFixedReset | .digestFinalizeReset =>
        (Operand.mem (outputSlot initial v mode keccak fullState) : Operand 64).read s = initial.regValue .r9 ∧
        (if firstCount mode inputs split = 0 then
          (if fullState then Operand.mem (frameBase initial v mode keccak fullState + 16)
            else (Operand.reg 5 : Operand 64)).read s = initial.regValue .rcx
        else (Operand.mem (frameBase initial v mode keccak fullState + if fullState then 16 else 8) : Operand 64).read s = initial.regValue .rcx)
    | .digest => False.elim (hMode rfl)
  countAtZero : firstCount mode inputs split = 0 → s.regValue .r15 = initial.regValue .rsi

theorem absorbed_zero (v : Variant) (inputs : Array Input) :
    Loop.absorbed v inputs 0 0 = Incremental.initial := by
  have he : inputs.extract 0 0 = #[] := Array.extract_eq_empty_of_le (by omega)
  simp only [Loop.absorbed, he, Incremental.message_empty, Incremental.canonicalState_empty]

theorem plain_through_first_loop [bindings : Bindings] {initial : RamState} {v : Variant} {keccak fullState : Bool}
    {inputs : Array Input} {split : Nat}
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hEnvironment : MachineRamUnitStrideDecodable bindings initial)
    (hCall : ValidInvocation (keccak := keccak) (fullState := fullState) bindings v .plain initial inputs split)
    (updateCorrect : Loop.UpdateCorrect v (returnBoundary initial)) :
    nearReturn64Boundary initial = .ok (returnBoundary initial) ∧
      ∃ fuel t, Advances (returnBoundary initial) fuel initial t ∧
        FirstResult (keccak := keccak) (fullState := fullState) initial v .plain inputs split t := by
  obtain ⟨hreturn, s, hsRun, hsInv, hsRip, hsInit, hsArgs, hsMemset⟩ :=
    entry_initialized hMachine hEnvironment hCall
  obtain ⟨n, u, huRun, huInv, huRip, huFrame, huPositive⟩ :=
    Selection.plain_selection (returnBoundary initial) hCall hsInv (by
      change stackPtr s ≠ (returnBoundary initial).rsp
      rw [hsInit.stack]
      exact frameBase_ne_returnBoundary (keccak := keccak) (fullState := fullState) initial v .plain)
      (by cases fullState <;> cases keccak <;> cases v <;> simpa only [Mode.initializedAddress, Mode.memsetCall, Mode.setupLength, Mode.setupOffset, pushOffset, Mode.pushCount, Nat.reduceMul, Bool.false_eq_true, false_and, and_false, reduceCtorEq, Bool.true_eq_false,
        Mode.entry, Selection.plainTestOffset, reduceCtorEq, Bool.true_eq_false, and_true, ↓reduceIte, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using hsRip)
      hsInit.stack hsArgs.count
  have huMem : u.external = s.external := huFrame.external (by
    simp [Selection.plainChanges, Component.Covers])
  have huSaved := hsInit.saved.of_external_eq huMem
  have huState := hsInit.stateAt.of_bytes_eq (by intro i hi; rw [huMem])
  have huStack : stackPtr u = frameBase (keccak := keccak) (fullState := fullState) initial v .plain :=
    (huFrame.read (n := 64) (r := 4) (by decide)).trans hsInit.stack
  have huPointers : u.regValue .r12 = initial.regValue .rdi :=
    (huFrame.read (n := 64) (r := 12) (by decide)).trans hsArgs.pointers
  have huLengths : u.regValue .r14 = initial.regValue .rdx :=
    (huFrame.read (n := 64) (r := 14) (by decide)).trans hsArgs.lengths
  have huCount : u.regValue .r15 = initial.regValue .rsi :=
    (huFrame.read (n := 64) (r := 15) (by decide)).trans hsArgs.count
  have huOutput : (Operand.mem (outputSlot (keccak := keccak) (fullState := fullState) initial v .plain) : Operand 64).read u =
      initial.regValue .rcx := by
    change memLoad u.external _ 64 = _
    rw [huMem]
    exact hsArgs.modeValues
  have hcount := hCall.inputSlices.countArgumentMatchesInputs
  by_cases hzero : initial.regValue .rsi = (0 : BitVec 64)
  · have hempty : inputs.size = 0 := by simpa [hzero] using hcount.symm
    refine ⟨hreturn, _, u, hsRun.trans huRun, huInv, huSaved, huStack, huPointers,
      huLengths, huCount, by simp, ?_, ?_, huOutput, (fun _ ↦ huCount)⟩
    · simpa only [firstCount, hempty, absorbed_zero] using huState
    · simpa only [hzero, ↓reduceIte, firstExit, Mode.entry] using huRip
  · have hzero' : initial.regValue .rsi ≠ 0#64 := hzero
    have hpos : 0 < inputs.size := by
      rw [← hcount]
      have hn : (initial.regValue .rsi).toNat ≠ 0 := by
        intro hn
        exact hzero (BitVec.eq_of_toNat_eq hn)
      omega
    have huLoop : Loop.State (keccak := keccak) (fullState := fullState) initial v .plain inputs 0 inputs.size 0 u := by
      refine ⟨huInv, ⟨huSaved.saved, huSaved.returnSlot⟩, ⟨huStack, huPointers, huLengths, ?_, (huPositive hzero).2.1, fun r hr ↦ by cases (Option.some.inj hr); exact (huPositive hzero).2.2⟩,
        (huPositive hzero).1, ?_⟩
      · change u.regValue .r15 = BitVec.ofNat 64 inputs.size
        rw [huCount, ← hcount, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      · simpa only [absorbed_zero, Loop.Kind.mode] using huState
    obtain ⟨fuel, t, htRun, htLoop, htRip, htFrame, _⟩ :=
      Loop.advance_with_update hCall
        (validInvocation_returnBoundary_bounds (Invariant.initial hMachine hEnvironment hCall).ready
          hCall).2 updateCorrect (by omega) (by omega) (by omega) huLoop (by
        simpa only [Loop.position, hpos, ↓reduceIte, Loop.Kind.start, Loop.Kind.mode,
          Mode.entry, hzero, hzero', BitVec.ofNat_eq_ofNat, BitVec.ofNat_eq_ofNat] using huRip)
    refine ⟨hreturn, _, t, (hsRun.trans huRun).trans htRun,
      htLoop.invariant, ⟨htLoop.saved.saved, htLoop.saved.returnSlot⟩, htLoop.registers.stack,
      htLoop.registers.pointers, htLoop.registers.lengths, ?_, by simp,
      htLoop.state, ?_, ?_, (fun hz ↦ (Nat.ne_of_gt hpos hz).elim)⟩
    · have hb : t.regValue .r15 = BitVec.ofNat 64 inputs.size := htLoop.registers.bound
      rw [← hcount, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hb
      exact hb
    · simpa only [firstExit, Loop.Kind.exit, Loop.Kind.endOffset, Loop.Kind.branchOffset, Loop.Kind.compareOffset, Loop.Kind.memoryBound, Loop.Kind.largeFollower, Loop.Kind.cursorReg, Option.isSome_some, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Loop.Kind.returnOffset, Loop.Kind.callOffset, Loop.Kind.stateOffset, Loop.Kind.start, Loop.Kind.mode, Mode.entry,
        Nat.reduceAdd, BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using htRip
    · have hslot := Loop.preserves_slot (offset := Mode.plain.outputSlotOffset v keccak fullState) htFrame
        (by cases fullState <;> cases keccak <;> cases v <;> decide)
      exact hslot.trans huOutput

theorem reset_through_first_loop [bindings : Bindings] {initial : RamState} {v : Variant} {keccak fullState : Bool}
    {inputs : Array Input} {split : Nat}
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hEnvironment : MachineRamUnitStrideDecodable bindings initial)
    (hCall : ValidInvocation (keccak := keccak) (fullState := fullState) bindings v .reset initial inputs split)
    (updateCorrect : Loop.UpdateCorrect v (returnBoundary initial)) :
    nearReturn64Boundary initial = .ok (returnBoundary initial) ∧
      ∃ fuel t, Advances (returnBoundary initial) fuel initial t ∧
        FirstResult (keccak := keccak) (fullState := fullState) initial v .reset inputs split t := by
  obtain ⟨hreturn, s, hsRun, hsInv, hsRip, hsInit, hsArgs, hsMemset⟩ :=
    entry_initialized hMachine hEnvironment hCall
  obtain ⟨n, u, huRun, huInv, huRip, huBound, huFrame, huPositive, huZeroBefore, huSavedCount⟩ :=
    Selection.reset_selection (forward := false) (copied := false) (returnBoundary initial) false hCall hsInv (by
      change stackPtr s ≠ (returnBoundary initial).rsp
      rw [hsInit.stack]
      exact frameBase_ne_returnBoundary (keccak := keccak) (fullState := fullState) initial v .reset)
      (by simpa only [Mode.initializedAddress, Mode.memsetCall, Mode.setupLength, Mode.setupOffset, pushOffset, Mode.pushCount, Nat.reduceMul, Bool.false_eq_true, false_and, and_false, reduceCtorEq, Bool.true_eq_false,
        Mode.entry, Selection.plainTestOffset, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd,
        Selection.testAddress, Selection.resetMode, Bool.false_eq_true, ↓reduceIte] using hsRip)
      hsInit.stack (initial.regValue .r8) (initial.regValue .rsi)
      hsArgs.modeValues.1 hsArgs.count hsArgs.modeValues.2.1
  have huInit := Selection.reset_initialized (forward := false) (copied := false) hsInit huFrame
  have huState := huInit.stateAt
  have huTables := Selection.reset_table_registers (forward := false) (copied := false) huFrame
  have huPointers : u.regValue .r12 = initial.regValue .rdi :=
    huTables.1.trans hsArgs.pointers
  have huLengths : u.regValue .r14 = initial.regValue .rdx :=
    huTables.2.1.trans hsArgs.lengths
  have huCount : u.regValue .r15 = initial.regValue .rsi :=
    huTables.2.2.trans hsArgs.count
  have huSlot : (Operand.mem (outputSlot (keccak := keccak) (fullState := fullState) initial v .reset) : Operand 64).read u =
      initial.regValue .rcx := (Selection.reset_outputSlot (forward := false) (copied := false) huFrame).trans hsArgs.modeValues.2.2
  have hcount := hCall.inputSlices.countArgumentMatchesInputs
  have hsplit := hCall.call.splitArgumentMatchesSplit
  have hSplitZero : initial.regValue .r8 = 0#64 ↔ split = 0 := by
    constructor
    · intro hz
      simpa only [hz, BitVec.toNat_ofNat, Nat.zero_mod] using hsplit.symm
    · intro hz
      exact BitVec.eq_of_toNat_eq (hsplit.trans hz)
  have hCountZero : initial.regValue .rsi = 0#64 ↔ inputs.size = 0 := by
    constructor
    · intro hz
      simpa only [hz, BitVec.toNat_ofNat, Nat.zero_mod] using hcount.symm
    · intro hz
      exact BitVec.eq_of_toNat_eq (hcount.trans hz)
  have hzeroIff : (initial.regValue .r8 = 0#64 ∨ initial.regValue .rsi = 0#64) ↔
      min split inputs.size = 0 := by
    rw [hSplitZero, hCountZero]
    omega
  have huBound' : u.regValue .rbx = BitVec.ofNat 64 (min split inputs.size) := by
    change u.regValue .rbx = _ at huBound
    simpa only [hsplit, hcount] using huBound
  by_cases hzero : initial.regValue .r8 = 0#64 ∨ initial.regValue .rsi = 0#64
  · have hmin : min split inputs.size = 0 := hzeroIff.mp hzero
    refine ⟨hreturn, _, u, hsRun.trans huRun, huInv, huInit.saved, huInit.stack,
      huPointers, huLengths, huCount, fun _ ↦ huBound', ?_, ?_, ?_, (fun _ ↦ huCount)⟩
    · simpa only [firstCount, hmin, absorbed_zero, Selection.resetMode, Bool.false_eq_true, ↓reduceIte] using huState
    · simpa only [hzero, ↓reduceIte, firstExit, firstCount, hmin, Selection.skipAddress,
        Selection.resetMode, Bool.false_eq_true, Mode.entry, BitVec.ofNat_eq_ofNat] using huRip
    · exact huSlot
  · have hpos : 0 < min split inputs.size := by
      have hn : min split inputs.size ≠ 0 := fun hz ↦ hzero (hzeroIff.mpr hz)
      omega
    have huLoop : Loop.State (keccak := keccak) (fullState := fullState) initial v .firstReset inputs 0 (min split inputs.size) 0 u := by
      refine ⟨huInv, ⟨huInit.saved.saved, huInit.saved.returnSlot⟩, ⟨huInit.stack, huPointers, huLengths,
        huBound', (huPositive hzero).2.1, by intro r h; cases h⟩, (huPositive hzero).1, ?_⟩
      simpa only [absorbed_zero, Loop.Kind.mode, Selection.resetMode, Bool.false_eq_true, ↓reduceIte] using huState
    obtain ⟨fuel, t, htRun, htLoop, htRip, htFrame, _⟩ :=
      Loop.advance_with_update hCall
        (validInvocation_returnBoundary_bounds (Invariant.initial hMachine hEnvironment hCall).ready
          hCall).2 updateCorrect (by omega) (by omega) (Nat.min_le_right _ _) huLoop (by
        simpa only [Loop.position, hpos, ↓reduceIte, Loop.Kind.start, Loop.Kind.mode,
          Mode.entry, hzero, firstKind, Loop.Kind.start, Selection.resetMode, Bool.false_eq_true, BitVec.ofNat_eq_ofNat] using huRip)
    have htSlot : (Operand.mem (outputSlot (keccak := keccak) (fullState := fullState) initial v .reset) : Operand 64).read t =
        (Operand.mem (outputSlot (keccak := keccak) (fullState := fullState) initial v .reset) : Operand 64).read u := by
      simpa only [outputSlot, Mode.outputSlotOffset, Loop.Kind.mode] using
        Loop.preserves_slot (offset := 0) htFrame (by cases fullState <;> cases keccak <;> cases v <;> decide)
    refine ⟨hreturn, _, t, (hsRun.trans huRun).trans htRun,
      htLoop.invariant, ⟨htLoop.saved.saved, htLoop.saved.returnSlot⟩, htLoop.registers.stack,
      htLoop.registers.pointers, htLoop.registers.lengths, ?_,
      fun _ ↦ htLoop.registers.bound, htLoop.state, ?_, ?_, (fun hz ↦ (Nat.ne_of_gt hpos hz).elim)⟩
    · exact (htFrame.read (n := 64) (r := 15) (by
        simp [Loop.clobbers, Loop.extraClobbers, Loop.Kind.indexReg, Loop.Kind.nextReg, Loop.Kind.largeFollower])).trans huCount
    · simpa only [firstExit, firstCount, Nat.ne_of_gt hpos, ↓reduceIte,
        Loop.Kind.exit, Loop.Kind.endOffset, Loop.Kind.branchOffset, Loop.Kind.compareOffset, Loop.Kind.memoryBound, Loop.Kind.largeFollower, Loop.Kind.cursorReg, Option.isSome_some, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Loop.Kind.returnOffset, Loop.Kind.callOffset, Loop.Kind.stateOffset, Loop.Kind.start, Loop.Kind.mode, Mode.entry,
        Nat.reduceAdd, BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using htRip
    · exact htSlot.trans huSlot

set_option maxHeartbeats 1000000 in
theorem finalizeReset_through_first_loop [bindings : Bindings] {initial : RamState}
    {v : Variant} {keccak fullState forward copied : Bool} {inputs : Array Input} {split : Nat}
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hEnvironment : MachineRamUnitStrideDecodable bindings initial)
    (hCall : ValidInvocation bindings v (Selection.resetMode true forward copied) initial inputs split keccak fullState)
    (updateCorrect : Loop.UpdateCorrect v (returnBoundary initial)) :
    nearReturn64Boundary initial = .ok (returnBoundary initial) ∧
      ∃ fuel t, Advances (returnBoundary initial) fuel initial t ∧
        FirstResult initial v (Selection.resetMode true forward copied) inputs split t keccak fullState
          (by cases forward <;> cases copied <;> simp [Selection.resetMode]) := by
  let forwarding := forward
  let copying := copied
  cases forward <;> cases copied
  all_goals
    obtain ⟨hreturn, s, hsRun, hsInv, hsRip, hsInit, hsArgs, hsMemset⟩ :=
      entry_initialized hMachine hEnvironment hCall
    have hsValues :
        (Operand.reg (Selection.splitRegister (Selection.splitLayout v true forwarding copying fullState)) : Operand 64).read s = initial.regValue .r8 ∧
        (Selection.beforeOutputOperand initial v forwarding copying keccak fullState).read s = initial.regValue .rcx ∧
        (Operand.reg (Selection.boundRegister (Selection.splitLayout v true forwarding copying fullState)) : Operand 64).read s = 0 ∧
        (Operand.mem (outputSlot initial v (Selection.resetMode true forwarding copying) keccak fullState) : Operand 64).read s = initial.regValue .r9 := by
      cases fullState <;> cases v <;> exact hsArgs.modeValues
    have haddress : (Selection.resetMode true forwarding copying).initializedAddress v keccak fullState =
        Selection.testAddress v true keccak fullState forwarding copying := by
      cases fullState <;> cases keccak <;> cases v <;> rfl
    obtain ⟨n, u, huRun, huInv, huRip, huBound, huFrame, huPositive, huZeroBefore, huSavedCount⟩ :=
      Selection.reset_selection (forward := forwarding) (copied := copying) (returnBoundary initial) true hCall hsInv
        (by rw [show s.GPR[4] = stackPtr s from rfl, hsInit.stack]
            exact frameBase_ne_returnBoundary initial v _ keccak fullState)
        (hsRip.trans haddress) hsInit.stack (initial.regValue .r8) (initial.regValue .rsi)
        hsValues.1 hsArgs.count hsValues.2.2.1
    have huInit := Selection.reset_initialized (forward := forwarding) (copied := copying) hsInit huFrame
    have huState := huInit.stateAt
    have huTables := Selection.reset_table_registers (forward := forwarding) (copied := copying) huFrame
    have huPointers : u.regValue .r12 = initial.regValue .rdi := huTables.1.trans hsArgs.pointers
    have huLengths : u.regValue .r14 = initial.regValue .rdx := huTables.2.1.trans hsArgs.lengths
    have huR15 : u.regValue .r15 = initial.regValue .rsi := huTables.2.2.trans hsArgs.count
    have huSlot : (Operand.mem (outputSlot initial v (Selection.resetMode true forwarding copying) keccak fullState) : Operand 64).read u = initial.regValue .r9 :=
      (Selection.reset_outputSlot (forward := forwarding) (copied := copying) huFrame).trans hsValues.2.2.2
    have huCount : (if (firstKind (Selection.resetMode true forwarding copying)).largeFollower v fullState then
        (Operand.mem (frameBase initial v (Selection.resetMode true forwarding copying) keccak fullState + if fullState then 8 else 0) : Operand 64)
        else Operand.reg 15).read u = initial.regValue .rsi := by
      cases hc : (firstKind (Selection.resetMode true forwarding copying)).largeFollower v fullState
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact huR15
      · simpa only [hc, ↓reduceIte, Selection.countSlot] using (huSavedCount hc).trans hsArgs.count
    have hcount := hCall.inputSlices.countArgumentMatchesInputs
    have hsplit := hCall.call.splitArgumentMatchesSplit
    have hzeroIff : (initial.regValue .r8 = 0#64 ∨ initial.regValue .rsi = 0#64) ↔ min split inputs.size = 0 := by
      have hSplitZero : initial.regValue .r8 = 0#64 ↔ split = 0 := by
        constructor
        · intro hz; simpa only [hz, BitVec.toNat_ofNat, Nat.zero_mod] using hsplit.symm
        · intro hz; exact BitVec.eq_of_toNat_eq (hsplit.trans hz)
      have hCountZero : initial.regValue .rsi = 0#64 ↔ inputs.size = 0 := by
        constructor
        · intro hz; simpa only [hz, BitVec.toNat_ofNat, Nat.zero_mod] using hcount.symm
        · intro hz; exact BitVec.eq_of_toNat_eq (hcount.trans hz)
      rw [hSplitZero, hCountZero]
      omega
    have huBound' : (Operand.reg ((firstKind (Selection.resetMode true forwarding copying)).boundReg v fullState) : Operand 64).read u =
        BitVec.ofNat 64 (min split inputs.size) := by
      have hr : Selection.boundRegister (Selection.splitLayout v true forwarding copying fullState) =
          (firstKind (Selection.resetMode true forwarding copying)).boundReg v fullState := by
        cases fullState <;> cases v <;> rfl
      simpa only [hr, hsplit, hcount] using huBound
    by_cases hzero : initial.regValue .r8 = 0#64 ∨ initial.regValue .rsi = 0#64
    · have hmin := hzeroIff.mp hzero
      refine ⟨hreturn, _, u, hsRun.trans huRun, huInv, huInit.saved, huInit.stack,
        huPointers, huLengths, huCount, (fun _ ↦ huBound'), ?_, ?_, ⟨huSlot, ?_⟩, (fun _ ↦ huR15)⟩
      · change Update.StateAt _ (Loop.absorbed v inputs 0 (min split inputs.size)) u
        rw [hmin, absorbed_zero]
        exact huState
      · have hp := huRip
        simp only [hzero, ↓reduceIte] at hp
        dsimp only [firstExit, Selection.resetMode, forwarding, copying]
        simp only [firstCount, hmin, ↓reduceIte]
        exact hp
      · have hb := (huZeroBefore hzero rfl).trans hsValues.2.1
        dsimp only [firstCount, Selection.resetMode, forwarding, copying]
        simp only [hmin, ↓reduceIte]
        exact hb
    · have hpos : 0 < min split inputs.size := by
        have hn : min split inputs.size ≠ 0 := fun hz ↦ hzero (hzeroIff.mpr hz)
        omega
      have huLoop : Loop.State initial v (firstKind (Selection.resetMode true forwarding copying)) inputs 0
          (min split inputs.size) 0 u keccak fullState := by
        refine ⟨huInv, ⟨huInit.saved.saved, huInit.saved.returnSlot⟩,
          ⟨huInit.stack, huPointers, huLengths, huBound', (huPositive hzero).2.1, ?_⟩,
          (huPositive hzero).1, ?_⟩
        · cases fullState <;> cases v <;> intro r hr
          all_goals first
            | (solve | cases hr)
            | (cases Option.some.inj hr; exact (huPositive hzero).2.2.2 rfl)
        · rw [absorbed_zero]
          exact huState
      obtain ⟨fuel, t, htRun, htLoop, htRip, htFrame, _⟩ :=
        Loop.advance_with_update hCall
          (validInvocation_returnBoundary_bounds (Invariant.initial hMachine hEnvironment hCall).ready hCall).2
          updateCorrect (by omega) (by omega) (Nat.min_le_right _ _) huLoop
          (by simpa only [Loop.position, hpos, hzero, ↓reduceIte] using huRip)
      have htSlot : (Operand.mem (outputSlot initial v (Selection.resetMode true forwarding copying) keccak fullState) : Operand 64).read t =
          (Operand.mem (outputSlot initial v (Selection.resetMode true forwarding copying) keccak fullState) : Operand 64).read u := by
        have hs := Loop.preserves_slot (offset := (Selection.resetMode true forwarding copying).outputSlotOffset v keccak fullState)
          htFrame (by cases fullState <;> cases keccak <;> cases v <;> decide)
        simpa only [forwarding, copying, Selection.resetMode, Bool.false_eq_true, ↓reduceIte,
          firstKind, Loop.Kind.mode, outputSlot] using hs
      have htCount : (if (firstKind (Selection.resetMode true forwarding copying)).largeFollower v fullState then
          (Operand.mem (frameBase initial v (Selection.resetMode true forwarding copying) keccak fullState + if fullState then 8 else 0) : Operand 64)
          else Operand.reg 15).read t = initial.regValue .rsi := by
        cases hc : (firstKind (Selection.resetMode true forwarding copying)).largeFollower v fullState
        · have hr := (htFrame.read (n := 64) (r := 15) (by
            cases fullState <;> cases v <;>
              first
              | (solve | simp [forwarding, copying, firstKind, Selection.resetMode, Loop.Kind.largeFollower] at hc)
              | simp [forwarding, copying, firstKind, Selection.resetMode, Loop.Kind.largeFollower,
                  Loop.clobbers, Loop.extraClobbers, Loop.Kind.indexReg, Loop.Kind.nextReg])).trans huR15
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact hr
        · have hs := Loop.preserves_slot (offset := if fullState then 8 else 0) htFrame
            (by cases fullState <;> cases keccak <;> cases v <;> decide)
          have hu := huCount
          simp only [hc, ↓reduceIte] at hu ⊢
          cases fullState <;> exact hs.trans hu
      have huBefore := ((huPositive hzero).2.2.1 rfl).trans hsValues.2.1
      have htBefore := Loop.preserves_slot (offset := if copying && fullState then 16 else 8) htFrame
        (by cases fullState <;> cases keccak <;> cases v <;> decide)
      refine ⟨hreturn, _, t, (hsRun.trans huRun).trans htRun, htLoop.invariant,
        ⟨htLoop.saved.saved, htLoop.saved.returnSlot⟩, htLoop.registers.stack,
        htLoop.registers.pointers, htLoop.registers.lengths, htCount,
        (fun _ ↦ htLoop.registers.bound), htLoop.state, ?_, ⟨htSlot.trans huSlot, ?_⟩,
        (fun hz ↦ (Nat.ne_of_gt hpos hz).elim)⟩
      · simp only [Selection.resetMode, Bool.false_eq_true, ↓reduceIte]
        simp only [firstExit, firstCount, Nat.ne_of_gt hpos, ↓reduceIte]
        first
        | (have _hcopied : copying = true := rfl; exact htRip)
        | simpa only [forwarding, copying, Selection.resetMode, firstKind,
            Loop.Kind.exit, Loop.Kind.start, Loop.Kind.endOffset,
            Loop.Kind.branchOffset, Loop.Kind.compareOffset, Loop.Kind.returnOffset, Loop.Kind.callOffset,
            Loop.Kind.stateOffset, Loop.Kind.cursorReg, Loop.Kind.largeFollower, Loop.Kind.memoryBound,
            Loop.Kind.mode, Mode.entry, Bool.false_eq_true, ↓reduceIte, Nat.reduceAdd,
            BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Option.isSome_none,
            Option.isSome_some] using htRip
      · simp only [Selection.resetMode, Bool.false_eq_true, ↓reduceIte]
        simp only [firstCount, Nat.ne_of_gt hpos, ↓reduceIte]
        cases fullState <;> exact htBefore.trans huBefore


theorem through_first_loop [bindings : Bindings] {initial : RamState} {v : Variant}
    {keccak fullState : Bool} {mode : Mode} {inputs : Array Input} {split : Nat}
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hEnvironment : MachineRamUnitStrideDecodable bindings initial)
    (hCall : ValidInvocation bindings v mode initial inputs split keccak fullState)
    (updateCorrect : Loop.UpdateCorrect v (returnBoundary initial))
    (hMode : mode ≠ .digest := by decide) :
    nearReturn64Boundary initial = .ok (returnBoundary initial) ∧
      ∃ fuel t, Advances (returnBoundary initial) fuel initial t ∧
        FirstResult initial v mode inputs split t keccak fullState hMode := by
  cases mode with
  | plain => exact plain_through_first_loop hMachine hEnvironment hCall updateCorrect
  | reset => exact reset_through_first_loop hMachine hEnvironment hCall updateCorrect
  | finalizeReset => exact finalizeReset_through_first_loop (forward := false) (copied := false) hMachine hEnvironment hCall updateCorrect
  | digestFinalizeIntoReset => exact finalizeReset_through_first_loop (forward := true) (copied := false) hMachine hEnvironment hCall updateCorrect
  | finalizeFixedReset => exact finalizeReset_through_first_loop (forward := false) (copied := true) hMachine hEnvironment hCall updateCorrect
  | digestFinalizeReset => exact finalizeReset_through_first_loop (forward := true) (copied := true) hMachine hEnvironment hCall updateCorrect
  | digest => exact False.elim (hMode rfl)

end Sha3.Proofs.Wrapper.Setup

namespace Sha3.Proofs.Wrapper.Setup

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

set_option maxHeartbeats 800000 in
theorem digest_update_call [bindings : Bindings] {initial s : RamState}
    {v : Variant} {keccak fullState : Bool} {inputs : Array Input} {split : Nat}
    (hCall : ValidInvocation bindings v .digest initial inputs split keccak fullState)
    (inv : Invariant initial v .digest s keccak fullState)
    (initialized : Initialized initial v .digest s keccak fullState)
    (args : SetupArguments initial v .digest s keccak fullState)
    (ip : s.RIP = (Mode.digest.entry v keccak fullState).entryAddress +
      Selection.digestArgumentsOffset v fullState)
    (hDigestMemset : fullState = true → s.regValue .r13 = 0x106a20 := by simp_all) :
    ∃ called, Advances (returnBoundary initial) 5 s called ∧
      Invariant initial v .digest called keccak fullState ∧
      called.RIP = v.updateAddress ∧
      stackPtr called = frameBase initial v .digest keccak fullState - 8 ∧
      stackTop called = Finish.startAddress .digest v keccak fullState ∧
      SavedFrame initial called .digest fullState ∧
      Update.StateAt (statePointer initial v .digest keccak fullState) Incremental.initial called ∧
      called.regValue .rdi = statePointer initial v .digest keccak fullState + 200 ∧
      called.regValue .rsi = statePointer initial v .digest keccak fullState ∧
      called.regValue .rdx = initial.regValue .rdi ∧
      called.regValue .rcx = initial.regValue .rsi ∧
      called.regValue .r12 = statePointer initial v .digest keccak fullState ∧
      called.regValue .rbx = initial.regValue .rdx ∧
      called.regValue .rbp = initial.regValue .rbp ∧
      (fullState = false → called.regValue .r13 = initial.regValue .r13) ∧
      (fullState = true → called.regValue .r13 = 0x106a20) := by
  obtain ⟨prepared, hpRun, hpInv, _, hpRip, hpCursor, hpPointer, hpInput, hpLength, hpFrame⟩ :=
    Selection.digest_arguments (returnBoundary initial) hCall inv (by
      change stackPtr s ≠ _
      rw [initialized.stack]
      apply Finish.stackSub_ne_returnBoundary
      cases keccak <;> cases fullState <;> cases v <;> decide)
      ip initialized.stack args.modeValues.2.1 args.pointers args.lengths
  have hpStack : stackPtr prepared = frameBase initial v .digest keccak fullState :=
    (hpFrame.read (r := 4) (n := 64) (by decide)).trans initialized.stack
  have hpMem : prepared.external = s.external := hpFrame.external (by
    simp [Selection.digestArgumentChanges, Component.Covers])
  have hpSaved := initialized.saved.of_external_eq hpMem
  have hpState := initialized.stateAt.of_bytes_eq (by intro j hj; rw [hpMem])
  let p := (Mode.digest.entry v keccak fullState).entryAddress +
    Selection.digestArgumentsOffset v fullState + (17 : BitVec 64)
  let disp := (v.updateAddress - (p + 5)).setWidth 32
  have target : branchTarget p 5 (disp.signExtend 64) = v.updateAddress := by
    cases keccak <;> cases fullState <;> cases v <;> decide +kernel
  have imageAt : ImageAt p (encodeCallRel32 disp) := by
    cases fullState with
    | false => cases keccak <;> cases v <;> unfold ImageAt <;> decide +kernel
    | true =>
      obtain ⟨rfl, rfl⟩ := hCall.fullState_valid rfl
      unfold ImageAt
      decide +kernel
  have image : ∀ x ∈ codeRange p (encodeCallRel32 disp), x ∈ Extracted.programImage :=
    fun x hx ↦ imageSections_mem_toCodeMap_of_fetchByte (imageAt x hx).2
  obtain ⟨called, hcRun, hcInv, hcRip, hcStack, hcTop, hcFrame, hcEffect⟩ :=
    Finish.directCallAt (Mode.digest.frameSize v keccak fullState) p disp hCall
      (by rw [Mode.stackBudget .digest v keccak fullState]; omega)
      (by cases keccak <;> cases fullState <;> cases v <;> decide)
      hpInv hpRip hpStack image (by rw [target]; cases v <;> decide)
  have hcStack' : stackPtr called = frameBase initial v .digest keccak fullState - 8 := by
    simpa only [frameBase_sub_eight (keccak := keccak) (fullState := fullState)] using hcStack
  have hcFrame' : AgreesExcept
      [.reg 4, .mem (frameBase initial v .digest keccak fullState - 8) 8, .rip]
      prepared called := by
    simpa only [frameBase_sub_eight (keccak := keccak) (fullState := fullState)] using hcFrame
  have hcSaved : SavedFrame initial called .digest fullState :=
    hpSaved.of_localFrame (v := v) (keccak := keccak) hcFrame' (by
      intro c hc address hCover
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact hCover.elim
      · obtain ⟨j, hj, he⟩ := hCover
        exact ⟨j, by cases keccak <;> cases fullState <;> cases v <;>
          simp only [Mode.frameSize, Mode.pushCount, Bool.false_eq_true, ↓reduceIte] <;> omega, he⟩
      · exact hCover.elim)
  have hcState : Update.StateAt (statePointer initial v .digest keccak fullState)
      Incremental.initial called := by
    apply hpState.of_bytes_eq
    intro j hj
    have he := Finish.callMemory_above hcEffect
      (offset := Mode.digest.stateOffset v keccak fullState) (count := 201)
      (by cases keccak <;> cases fullState <;> cases v <;> decide) j hj
    simpa only [hpStack, statePointer] using he
  refine ⟨called, hpRun.trans hcRun, hcInv, hcRip.trans target, hcStack', ?_, hcSaved,
    hcState, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hcTop.trans (by
      cases keccak <;> cases fullState <;> cases v <;> decide +kernel)
  · exact (hcFrame'.read (r := 7) (n := 64) (by simp)).trans hpCursor
  · exact (hcFrame'.read (r := 6) (n := 64) (by simp)).trans hpPointer
  · exact (hcFrame'.read (r := 2) (n := 64) (by simp)).trans hpInput
  · exact (hcFrame'.read (r := 1) (n := 64) (by simp)).trans hpLength
  · exact (hcFrame'.read (r := 12) (n := 64) (by simp)).trans
      ((hpFrame.read (r := 12) (n := 64) (by decide)).trans args.modeValues.2.1)
  · exact (hcFrame'.read (r := 3) (n := 64) (by simp)).trans
      ((hpFrame.read (r := 3) (n := 64) (by decide)).trans args.modeValues.1)
  · exact (hcFrame'.read (r := 5) (n := 64) (by simp)).trans
      ((hpFrame.read (r := 5) (n := 64) (by decide)).trans args.modeValues.2.2.1)
  · intro hfull
    exact (hcFrame'.read (r := 13) (n := 64) (by simp)).trans
      ((hpFrame.read (r := 13) (n := 64) (by decide)).trans (args.modeValues.2.2.2 hfull))

  · intro hfull
    exact (hcFrame'.read (r := 13) (n := 64) (by simp)).trans
      ((hpFrame.read (r := 13) (n := 64) (by decide)).trans (hDigestMemset hfull))

theorem digest_initialized_update [bindings : Bindings] {initial s : RamState}
    {v : Variant} {keccak fullState : Bool} {inputs : Array Input} {split : Nat}
    (hCall : ValidInvocation bindings v .digest initial inputs split keccak fullState)
    (inv : Invariant initial v .digest s keccak fullState)
    (initialized : Initialized initial v .digest s keccak fullState)
    (args : SetupArguments initial v .digest s keccak fullState)
    (ip : s.RIP = (Mode.digest.entry v keccak fullState).entryAddress +
      Selection.digestArgumentsOffset v fullState)
    (updateCorrect : Loop.UpdateCorrect v (returnBoundary initial))
    (hDigestMemset : fullState = true → s.regValue .r13 = 0x106a20 := by simp_all) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧
      Invariant initial v .digest t keccak fullState ∧
      SavedFrame initial t .digest fullState ∧
      t.RIP = Finish.startAddress .digest v keccak fullState ∧
      stackPtr t = frameBase initial v .digest keccak fullState ∧
      Update.StateAt (statePointer initial v .digest keccak fullState)
        (Incremental.canonicalState Keccak.keccakLanes v.rate (message inputs)) t ∧
      t.regValue .r12 = statePointer initial v .digest keccak fullState ∧
      t.regValue .rbx = initial.regValue .rdx ∧
      t.regValue .rbp = initial.regValue .rbp ∧
      (fullState = false → t.regValue .r13 = initial.regValue .r13) ∧
      (fullState = true → t.regValue .r13 = 0x106a20) := by
  obtain ⟨called, hcRun, hcInv, hcRip, hcStack, hcTop, hcSaved, hcState,
    hcCursor, hcPointer, hcInput, hcLength, hcR12, hcOutput, hcRbp, hcR13, hcMemset⟩ :=
    digest_update_call hCall inv initialized args ip hDigestMemset
  obtain ⟨data, hinputs, hd⟩ := hCall.call
  let input : Input := ⟨initial.regValue .rdi, data⟩
  have hmessage : message inputs = data := by
    rw [hinputs]
    simp [message]
  have hRegs : Loop.UpdateEntryRegisters initial v .plain input called keccak fullState .digest :=
    ⟨hcStack, hcPointer, hcInput, hcLength.trans (by
      rw [← hd.lengthArgumentMatchesData, BitVec.ofNat_toNat, BitVec.setWidth_eq]), hcCursor⟩
  have hTarget : InProgram (stackTop called) := by
    rw [hcTop]
    let byte : UInt8 := if fullState then 0x4c else if v = .sha224 then 0xc7 else 0x48
    refine ⟨byte, imageSections_mem_toCodeMap_of_fetchByte ?_⟩
    cases fullState <;> cases keccak <;> cases v <;> decide +kernel
  have context := Loop.update_callContext input hCall hcInv hd.inputInMemory
    (by simp [hinputs, invocationReadRegions, input]) hRegs hcRip hcState
    (by simpa only [Incremental.initial] using v.rate_pos) hTarget
  obtain ⟨fuel, t, huRun, huReady, _, huResult⟩ :=
    updateCorrect called data Incremental.initial context
  have hFits : Mode.digest.savedBytes fullState ≤
      (Mode.digest.entry v keccak fullState).minStackBytes := by
    rw [Mode.stackBudget .digest v keccak fullState]
    cases fullState <;> cases keccak <;> cases v <;> decide
  have huInv := hcInv.of_callResult hCall huReady huResult.memory
    (Loop.update_writeRegions_subset_outer hCall.stackAvailable hcStack hcPointer)
    huResult.grows huResult.rest
  have huSaved := Loop.savedFrame_of_memoryWriteFrame hcSaved hCall.stackAvailable
    huResult.memory hFits
    (fun region hr ↦ (Loop.update_writeRegions_bounds hCall.stackAvailable hcStack hcPointer hr).2)
  refine ⟨_, t, hcRun.trans huRun, huInv, huSaved, huResult.rip.trans hcTop, ?_, ?_,
    (huResult.saved .r12 (by simp)).trans hcR12,
    (huResult.saved .rbx (by simp)).trans hcOutput,
    (huResult.saved .rbp (by simp)).trans hcRbp,
    fun h ↦ (huResult.saved .r13 (by simp)).trans (hcR13 h),
    fun h ↦ (huResult.saved .r13 (by simp)).trans (hcMemset h)⟩
  · change t.regValue .rsp = _
    rw [huResult.stack]
    change stackPtr called + 8 = _
    rw [hcStack, BitVec.sub_add_cancel]
  · have hs := huResult.state
    rw [hcPointer, Incremental.update_initial _ _ v.rate_pos, ← hmessage] at hs
    exact hs

theorem digest_through_update [bindings : Bindings] {initial : RamState}
    {v : Variant} {keccak fullState : Bool} {inputs : Array Input} {split : Nat}
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hEnvironment : MachineRamUnitStrideDecodable bindings initial)
    (hCall : ValidInvocation bindings v .digest initial inputs split keccak fullState)
    (updateCorrect : Loop.UpdateCorrect v (returnBoundary initial)) :
    nearReturn64Boundary initial = .ok (returnBoundary initial) ∧
      ∃ fuel t, Advances (returnBoundary initial) fuel initial t ∧
        Invariant initial v .digest t keccak fullState ∧
        SavedFrame initial t .digest fullState ∧
        t.RIP = Finish.startAddress .digest v keccak fullState ∧
        stackPtr t = frameBase initial v .digest keccak fullState ∧
        Update.StateAt (statePointer initial v .digest keccak fullState)
          (Incremental.canonicalState Keccak.keccakLanes v.rate (message inputs)) t ∧
        t.regValue .rbx = initial.regValue .rdx ∧
        t.regValue .r12 = statePointer initial v .digest keccak fullState ∧
        (∀ j : Fin 6,
          (∀ i : Fin (Mode.digest.pushCount fullState),
            (Finish.epiloguePopReg .digest fullState i).setWidth 5 ≠
              (Finish.epiloguePopReg .plain false j).setWidth 5) →
          (Operand.reg ((Finish.epiloguePopReg .plain false j).setWidth 5) : Operand 64).read t =
            initial.regValue savedRegisters[j]) ∧
        (fullState = true → t.regValue .r13 = 0x106a20) := by
  obtain ⟨hreturn, s, hsRun, hsInv, hsRip, hsInit, hsArgs, hsMemset⟩ :=
    entry_initialized hMachine hEnvironment hCall
  have hstart : Mode.digest.initializedAddress v keccak fullState =
      (Mode.digest.entry v keccak fullState).entryAddress +
        Selection.digestArgumentsOffset v fullState := by
    cases fullState <;> cases keccak <;> cases v <;> rfl
  obtain ⟨fuel, t, htRun, htInv, htSaved, htRip, htStack, htState,
    htR12, htOutput, htRbp, htR13, htMemset⟩ :=
    digest_initialized_update hCall hsInv hsInit hsArgs (hsRip.trans hstart)
      updateCorrect (hsMemset rfl)
  refine ⟨hreturn, _, t, hsRun.trans htRun, htInv, htSaved, htRip, htStack,
    htState, htOutput, htR12, ?_, htMemset⟩
  intro j hnot
  have select : ∀ f : Bool, ∀ k : Fin 6,
      (∀ i : Fin (Mode.digest.pushCount f),
        (Finish.epiloguePopReg .digest f i).setWidth 5 ≠
          (Finish.epiloguePopReg .plain false k).setWidth 5) →
      k.val = 5 ∨ (f = false ∧ k.val = 2) := by decide +kernel
  rcases select fullState j hnot with hj | ⟨hf, hj⟩
  · have he : j = ⟨5, by decide⟩ := Fin.ext hj
    subst j
    exact htRbp
  · have he : j = ⟨2, by decide⟩ := Fin.ext hj
    subst j
    exact htR13 hf

end Sha3.Proofs.Wrapper.Setup