import Sha3.Proofs.Wrapper.Setup.Prologue
import Sha3.Proofs.Wrapper.Setup.Prefix
import Sha3.Proofs.Wrapper.Setup.Digest
import Sha3.Proofs.Wrapper.Setup.Initialize

namespace Sha3.Proofs.Wrapper

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

def Mode.setupBytes (mode : Mode) (v : Variant) (_keccak fullState : Bool := false) : List UInt8 :=
  match mode with
  | .plain => plainSetupBytes v fullState
  | .reset => resetSetupBytes
  | .finalizeReset | .finalizeFixedReset | .digestFinalizeIntoReset | .digestFinalizeReset => finalizeResetSetupBytes (finalizeResetStateAddr v mode fullState)
      (finalizeResetSwapped v mode fullState) (finalizeResetStored mode fullState)
  | .digest => digestSetupBytes v fullState

def Mode.setupSteps (mode : Mode) (fullState : Bool := false) : Nat :=
  match mode with
  | .plain => 7
  | .reset => 9
  | .finalizeReset | .finalizeFixedReset | .digestFinalizeIntoReset | .digestFinalizeReset => 10
  | .digest => if fullState then 8 else 7

def Mode.setupLength (mode : Mode) (v : Variant) (_keccak fullState : Bool := false) : Nat :=
  match mode, v with
  | .plain, .sha512 => if fullState then 25 else 29
  | .plain, _ => if fullState then 25 else 26
  | .reset, _ => 30
  | .finalizeReset, _ | .digestFinalizeIntoReset, _ => 35
  | .finalizeFixedReset, _ | .digestFinalizeReset, _ => if fullState then 36 else if finalizeResetSwapped v mode fullState then 37 else 38
  | .digest, _ => digestSetupTail v fullState + 10

def Mode.setupOffset (mode : Mode) (fullState : Bool := false) : Nat :=
  pushOffset (mode.pushCount fullState) mode fullState + 7

def Mode.memsetCall (mode : Mode) (v : Variant) (keccak fullState : Bool := false) : BitVec 64 :=
  (mode.entry v keccak fullState).entryAddress + BitVec.ofNat 64 ((mode.setupOffset fullState) + (mode.setupLength v keccak fullState))

def Mode.memsetDisp (mode : Mode) (v : Variant) (keccak fullState : Bool := false) : BitVec 32 :=
  (0x200188 - (mode.memsetCall v keccak fullState + 6)).setWidth 32

def Mode.initializedAddress (mode : Mode) (v : Variant) (keccak fullState : Bool := false) : BitVec 64 :=
  mode.memsetCall v keccak fullState + (if mode = .digest ∧ fullState then 3 else 6)

theorem setupImage (mode : Mode) (v : Variant) (keccak fullState : Bool := false) :
    ImageAt ((mode.entry v keccak fullState).entryAddress + BitVec.ofNat 64 (mode.setupOffset fullState))
      (mode.setupBytes v keccak fullState) := by
  cases fullState with
  | false =>
    cases keccak <;> cases mode <;> cases v <;>
      first | contradiction | (solve | simp_all) | (unfold ImageAt; decide +kernel)
  | true =>
    have hsame : ImageAt ((mode.entry v keccak true).entryAddress + BitVec.ofNat 64 (mode.setupOffset true)) (mode.setupBytes v keccak true) =
        ImageAt ((mode.entry .sha256 keccak true).entryAddress + BitVec.ofNat 64 (mode.setupOffset true)) (mode.setupBytes .sha256 keccak true) := by
      cases mode <;> cases v <;> first | (solve | simp_all) | rfl
    rw [hsame]
    cases keccak <;> cases mode <;>
      first | contradiction | (solve | simp_all) | (unfold ImageAt; decide +kernel)

theorem initialMemsetImage (mode : Mode) (v : Variant) (keccak fullState : Bool := false)
    (hindirect : ¬ (mode = .digest ∧ fullState = true) := by simp) :
    ImageAt (mode.memsetCall v keccak fullState)
      (encodeCallM64 (.rip (mode.memsetDisp v keccak fullState))) := by
  cases fullState with
  | false =>
    cases keccak <;> cases mode <;> cases v <;>
      first | contradiction | (solve | simp_all) | (unfold ImageAt; decide +kernel)
  | true =>
    have hsame : ImageAt (mode.memsetCall v keccak true) (encodeCallM64 (.rip (mode.memsetDisp v keccak true))) =
        ImageAt (mode.memsetCall .sha256 keccak true) (encodeCallM64 (.rip (mode.memsetDisp .sha256 keccak true))) := by
      cases mode <;> cases v <;> first | (solve | simp_all) | rfl
    rw [hsame]
    cases keccak <;> cases mode <;>
      first | contradiction | (solve | simp_all) | (unfold ImageAt; decide +kernel)

theorem initialMemsetRegisterImage (v : Variant) (keccak : Bool) :
    ImageAt (Mode.memsetCall .digest v keccak true) [0x41, 0xff, 0xd5] := by
  cases keccak <;> cases v <;> unfold ImageAt <;> decide +kernel

theorem memsetCall_target (mode : Mode) (v : Variant) (keccak fullState : Bool := false) :
    (mode.memsetCall v keccak fullState + 6) + (mode.memsetDisp v keccak fullState).signExtend 64 = 0x200188 := by
  cases keccak <;> cases fullState <;> cases mode <;> cases v <;> first | contradiction | (solve | simp_all) | decide +kernel

theorem memsetCall_retLow (mode : Mode) (v : Variant) (keccak fullState : Bool := false) :
    (mode.memsetCall v keccak fullState + (6 : BitVec 64)).toNat < 2^32 := by
  cases keccak <;> cases fullState <;> cases mode <;> cases v <;> decide +kernel

theorem memsetRegisterCall_retLow (v : Variant) (keccak : Bool) :
    (Mode.memsetCall .digest v keccak true + (3 : BitVec 64)).toNat < 2^32 := by
  cases keccak <;> cases v <;> decide +kernel

theorem frameBase_ne_returnBoundary (initial : RamState) (v : Variant) (mode : Mode) (keccak fullState : Bool := false) :
    frameBase initial v mode keccak fullState ≠ (returnBoundary initial).rsp := by
  change initial.regValue .rsp - BitVec.ofNat 64 (mode.frameSize v keccak fullState) ≠ initial.regValue .rsp + 8
  simp only [BitVec.sub_eq_add_neg, ne_eq, BitVec.add_right_inj]
  cases keccak <;> cases fullState <;> cases mode <;> cases v <;> decide

theorem frameBase_sub_eight_ne_returnBoundary (initial : RamState) (v : Variant) (mode : Mode) (keccak fullState : Bool := false) :
    frameBase initial v mode keccak fullState - 8 ≠ (returnBoundary initial).rsp := by
  rw [frameBase_sub_eight initial v mode keccak fullState]
  change initial.regValue .rsp - BitVec.ofNat 64 ((mode.frameSize v keccak fullState) + 8) ≠ initial.regValue .rsp + 8
  simp only [BitVec.sub_eq_add_neg, ne_eq, BitVec.add_right_inj]
  cases keccak <;> cases fullState <;> cases mode <;> cases v <;> decide

theorem setup_savedFrame {initial s t : RamState} {v : Variant} {mode : Mode} {keccak fullState : Bool}
    (saved : SavedFrame initial s mode fullState) (ha : AgreesExcept (setupChanges initial v mode keccak fullState) s t) :
    SavedFrame initial t mode fullState := by
  apply saved.of_localFrame (v := v) (mode := mode) (keccak := keccak) ha
  intro c hc address hcover
  simp only [setupChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hc
  all_goals try exact hcover.elim
  first | subst c | (rcases hc with rfl | rfl)
  all_goals obtain ⟨i, hi, rfl⟩ := hcover
  all_goals first
    | (solve
      | refine ⟨8 + mode.outputSlotOffset v keccak fullState + i, ?_, ?_⟩
        · have hb : 8 + mode.outputSlotOffset v keccak fullState + 8 ≤
              mode.frameSize v keccak fullState - (8 * mode.pushCount fullState - 8) := by
            cases keccak <;> cases fullState <;> cases mode <;> cases v <;> decide
          omega
        · simp only [outputSlot, BitVec.ofNat_add, ← BitVec.add_assoc,
            BitVec.ofNat_eq_ofNat, BitVec.sub_add_cancel])
    | refine ⟨24 + i, ?_, ?_⟩
      · have hb : 32 ≤ mode.frameSize v keccak fullState - (8 * mode.pushCount fullState - 8) := by
          cases keccak <;> cases fullState <;> cases mode <;> cases v <;> decide
        omega
      · simp only [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.ofNat_eq_ofNat]
        simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]


theorem SetupArguments.initialized {initial s t : RamState} {v : Variant} {mode : Mode} {keccak fullState : Bool}
    (args : SetupArguments initial v mode s keccak fullState)
    (ha : AgreesExcept (initializationChanges initial v mode keccak fullState) s t) :
    SetupArguments initial v mode t keccak fullState := by
  have hreg (r : BitVec 5) (hr : r ∈ [3, 5, 12, 13, 14, 15]) :
      (Operand.reg r : Operand 64).read t = (Operand.reg r : Operand 64).read s := by
    apply ha.read
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [initializationChanges, Memset.clobbers]
  have hslot := initialization_outputSlot ha
  have hslot16 (hstate : 32 ≤ mode.stateOffset v keccak fullState) :
      (Operand.mem (frameBase initial v mode keccak fullState + 16) : Operand 64).read t =
        (Operand.mem (frameBase initial v mode keccak fullState + 16) : Operand 64).read s := by
    apply readMem_agrees ha
    intro j hj comp hc hcover
    simp only [initializationChanges, List.mem_append, Memset.clobbers, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl) |
      (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals try exact hcover.elim
    · obtain ⟨i, hi, he⟩ := hcover
      have apart : OffsetsApart (-(8 : BitVec 64)) 8 16 8 := by unfold OffsetsApart; decide +kernel
      apply apart.ne (frameBase initial v mode keccak fullState) hi hj (by decide)
      simpa only [BitVec.sub_eq_add_neg] using he.symm
    · obtain ⟨i, hi, he⟩ := hcover
      have apart : OffsetsApart (BitVec.ofNat 64 (mode.stateOffset v keccak fullState)) 201 16 8 := by
        exact (by
          cases keccak <;> cases fullState <;> cases mode <;> cases v <;> unfold OffsetsApart <;> decide +kernel :
          32 ≤ mode.stateOffset v keccak fullState →
            OffsetsApart (BitVec.ofNat 64 (mode.stateOffset v keccak fullState)) 201 16 8) hstate
      apply apart.ne (frameBase initial v mode keccak fullState) hi hj (by decide)
      exact he.symm
  cases fullState <;> cases mode <;> cases v
  all_goals refine ⟨?_, ?_, ?_, ?_⟩
  all_goals first
    | exact (hreg 12 (by simp)).trans args.pointers
    | exact (hreg 15 (by simp)).trans args.pointers
    | exact (hreg 14 (by simp)).trans args.lengths
    | exact (hreg 15 (by simp)).trans args.count
    | trivial
    | exact hslot.trans args.modeValues
    | exact ⟨(hreg 13 (by simp)).trans args.modeValues.1,
        (hreg 3 (by simp)).trans args.modeValues.2.1, hslot.trans args.modeValues.2.2⟩
    | exact ⟨(hreg 3 (by simp)).trans args.modeValues.1,
        (hreg 12 (by simp)).trans args.modeValues.2.1,
        (hreg 5 (by simp)).trans args.modeValues.2.2.1,
        fun h => (hreg 13 (by simp)).trans (args.modeValues.2.2.2 h)⟩
    | exact ⟨(hreg 3 (by simp)).trans args.modeValues.1,
        (hreg 5 (by simp)).trans args.modeValues.2.1,
        (hreg 13 (by simp)).trans args.modeValues.2.2.1, hslot.trans args.modeValues.2.2.2⟩
    | exact ⟨(hreg 13 (by simp)).trans args.modeValues.1,
        (hreg 5 (by simp)).trans args.modeValues.2.1,
        (hreg 3 (by simp)).trans args.modeValues.2.2.1, hslot.trans args.modeValues.2.2.2⟩

    | exact ⟨(hreg 13 (by simp)).trans args.modeValues.1,
        (hslot16 (by cases keccak <;> decide)).trans args.modeValues.2.1,
        (hreg 3 (by simp)).trans args.modeValues.2.2.1, hslot.trans args.modeValues.2.2.2⟩

theorem setup_steps [bindings : Bindings] {initial s : RamState} {v : Variant} {mode : Mode} {keccak fullState : Bool}
    {inputs : Array Input} {split : Nat} (boundary : ReturnBoundary) (p : BitVec 64)
    (hCall : ValidInvocation bindings v mode initial inputs split keccak fullState)
    (image : ImageAt p (mode.setupBytes v keccak fullState)) (inv : Invariant initial v mode s keccak fullState)
    (ip : s.RIP = p) (sp : stackPtr s = frameBase initial v mode keccak fullState)
    (inside : s.GPR[4] ≠ boundary.rsp)
    (args : ∀ r ∈ [Syntax.Reg.rcx, .rdx, .rsi, .rdi, .r8, .r9, .rbp, .r13],
      s.regValue r = initial.regValue r) :
    ∃ t, Advances boundary (mode.setupSteps fullState) s t ∧ Invariant initial v mode t keccak fullState ∧
      t.RIP = p + BitVec.ofNat 64 (mode.setupLength v keccak fullState) ∧ SetupRegisters initial v mode t keccak fullState ∧
      SetupArguments initial v mode t keccak fullState ∧
      (mode = .digest → fullState = true → (Operand.reg 13 : Operand 64).read t = p + 0x49e0) ∧ AgreesExcept (setupChanges initial v mode keccak fullState) s t := by
  have argsMain : ∀ r ∈ [Syntax.Reg.rcx, .rdx, .rsi, .rdi, .r8, .r9],
      s.regValue r = initial.regValue r := by
    intro r hr
    apply args r
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  cases mode with
  | plain =>
    have h := plain_setup_steps boundary p hCall image inv ip sp inside argsMain
    obtain ⟨t, ht, hi, hip, hr, ha, hf⟩ := h
    refine ⟨t, ?_, hi, ?_, hr, ha, by intro h; contradiction, hf⟩
    · exact ht
    · cases fullState <;> cases v <;> exact hip
  | reset =>
    obtain ⟨t, ht, hi, hip, hr, ha, hf⟩ := reset_setup_steps boundary p hCall image inv ip sp inside argsMain
    exact ⟨t, ht, hi, hip, hr, ha, by intro h; contradiction, hf⟩
  | digest =>
    obtain ⟨t, ht, hi, hip, hr, ha, htarget, hf⟩ := digest_setup_steps boundary p hCall image inv ip sp inside
      (by intro r hr; apply args r; simpa only [List.mem_cons, List.not_mem_nil, or_false] using
        (show r = .rcx ∨ r = .rdx ∨ r = .rsi ∨ r = .rdi ∨ r = .r8 ∨ r = .r9 ∨ r = .rbp ∨ r = .r13 from by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp))
    exact ⟨t, ht, hi, hip, hr, ha, fun _ => htarget, hf⟩
  | finalizeReset | finalizeFixedReset | digestFinalizeIntoReset | digestFinalizeReset =>
    have h := finalizeReset_setup_steps boundary p hCall image inv ip sp inside argsMain
      (by simp)
    obtain ⟨t, ht, hi, hip, hr, ha, hf⟩ := h
    refine ⟨t, ht, hi, ?_, hr, ha, by intro h; contradiction, hf⟩
    cases fullState <;> cases v <;> exact hip

theorem entry_initialized [bindings : Bindings] {initial : RamState} {v : Variant}
    {mode : Mode} {keccak fullState : Bool} {inputs : Array Input} {split : Nat}
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hEnvironment : MachineRamUnitStrideDecodable bindings initial)
    (hCall : ValidInvocation bindings v mode initial inputs split keccak fullState)
 :
    nearReturn64Boundary initial = .ok (returnBoundary initial) ∧
      ∃ t, Advances (returnBoundary initial) (mode.pushCount fullState + 1 + mode.setupSteps fullState + 46) initial t ∧
        Invariant initial v mode t keccak fullState ∧ t.RIP = mode.initializedAddress v keccak fullState ∧
        Initialized initial v mode t keccak fullState ∧ SetupArguments initial v mode t keccak fullState ∧
        (mode = .digest → fullState = true → (Operand.reg 13 : Operand 64).read t = 0x106a20) := by
  have hi := Invariant.initial hMachine hEnvironment hCall
  obtain ⟨hreturn, hprologue, hpInv, hpSaved⟩ := entry_prologue hMachine hEnvironment hCall
  have hpRsp := prologueState_rsp initial v mode keccak fullState
  have hpRip := prologueState_rip hi hCall (by rw [Mode.stackBudget mode v keccak fullState]; omega)
  have hpArgs : ∀ r ∈ [Syntax.Reg.rcx, .rdx, .rsi, .rdi, .r8, .r9, .rbp, .r13],
      (prologueState initial v mode keccak fullState).regValue r = initial.regValue r := by
    generalize he : prologueState initial v mode keccak fullState = prologue
    have hregs := fun r hr => prologueState_register initial v mode r hr keccak fullState
    rw [he] at hregs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hregs 1 (by decide)
    · exact hregs 2 (by decide)
    · exact hregs 6 (by decide)
    · exact hregs 7 (by decide)
    · exact hregs 8 (by decide)
    · exact hregs 9 (by decide)
    · exact hregs 5 (by decide)
    · exact hregs 13 (by decide)
  obtain ⟨u, hprefix, huInv, huRip, huRegisters, huArgs, huTarget, huFrame⟩ :=
    setup_steps (returnBoundary initial) ((mode.entry v keccak fullState).entryAddress + BitVec.ofNat 64 (mode.setupOffset fullState)) hCall
      (setupImage mode v keccak fullState) hpInv hpRip hpRsp (by
        change stackPtr (prologueState initial v mode keccak fullState) ≠ (returnBoundary initial).rsp
        rw [hpRsp]
        exact frameBase_ne_returnBoundary initial v mode keccak fullState) hpArgs
  have huCall : u.RIP = mode.memsetCall v keccak fullState := by
    simpa only [Mode.memsetCall, BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using huRip
  have hbudget : mode.frameSize v keccak fullState + 8 ≤ (mode.entry v keccak fullState).minStackBytes := by
    rw [Mode.stackBudget mode v keccak fullState]
    omega
  have saved := setup_savedFrame hpSaved huFrame
  have before := frameBase_sub_eight_ne_returnBoundary initial v mode keccak fullState
  have after := frameBase_ne_returnBoundary initial v mode keccak fullState
  by_cases hregister : mode = .digest ∧ fullState = true
  · obtain ⟨rfl, rfl⟩ := hregister
    have target : (Operand.reg 13 : Operand 64).read u = 0x106a20 := by
      rw [huTarget rfl rfl]
      cases v <;> cases keccak <;> rfl
    obtain ⟨t, hmemset, htInv, htRip, htInitialized, htFrame, _⟩ :=
      initial_memset_register_steps hEnvironment.stringStride (returnBoundary initial)
        (Mode.memsetCall .digest v keccak true) hCall hbudget (initialMemsetRegisterImage v keccak)
        target (memsetRegisterCall_retLow v keccak) huInv saved huCall huRegisters before after
    refine ⟨hreturn, t, (hprologue.trans hprefix).trans hmemset,
      htInv, htRip, htInitialized, huArgs.initialized htFrame, ?_⟩
    intro _ _
    exact (htFrame.read (by simp [initializationChanges, Memset.clobbers])).trans target
  · obtain ⟨t, hmemset, htInv, htRip, htInitialized, htFrame, _⟩ :=
      initial_memset_steps hEnvironment.stringStride (returnBoundary initial)
        (mode.memsetCall v keccak fullState) (mode.memsetDisp v keccak fullState) hCall hbudget
        (initialMemsetImage mode v keccak fullState hregister)
        (memsetCall_target mode v keccak fullState) (memsetCall_retLow mode v keccak fullState)
        huInv saved huCall huRegisters before after
    exact ⟨hreturn, t, (hprologue.trans hprefix).trans hmemset,
      htInv, (by simpa only [Mode.initializedAddress, hregister, ↓reduceIte] using htRip),
      htInitialized, huArgs.initialized htFrame, by intro hm hf; exact (hregister ⟨hm, hf⟩).elim⟩

end Sha3.Proofs.Wrapper
