import Sha3.Proofs.Wrapper.Frame
import Sha3.Proofs.X86.Instructions.Sub.Imm32.Triple

namespace Sha3.Proofs.Wrapper

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

def pushSource (n : Nat) (mode : Mode := .plain) (fullState : Bool := false) : BitVec 4 :=
  match mode, fullState, n with
  | .digest, _, 0 => 15
  | .digest, _, 1 => 14
  | .digest, true, 2 => 13
  | .digest, true, 3 | .digest, false, 2 => 12
  | .digest, _, _ => 3
  | _, _, 0 => 5
  | _, _, 1 => 15
  | _, _, 2 => 14
  | _, _, 3 => 13
  | _, _, 4 => 12
  | _, _, _ => 3

def pushOffset (n : Nat) (mode : Mode := .plain) (fullState : Bool := false) : Nat :=
  match mode with
  | .digest => min (2 * n) (if fullState then 9 else 7)
  | _ => match n with
    | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 5 | 4 => 7 | 5 => 9 | _ => 10

def pushedState (initial : RamState) (n : Nat) (mode : Mode := .plain)
    (fullState : Bool := false) : RamState :=
  match n with
  | 0 => initial
  | n + 1 => pushAfter (pushedState initial n mode fullState) (pushSource n mode fullState)

theorem pushCount_le_six (mode : Mode) (fullState : Bool) : mode.pushCount fullState ≤ 6 := by
  cases mode <;> cases fullState <;> decide

def prologueCodeBytes (v : Variant) (mode : Mode) (keccak fullState : Bool := false) : List UInt8 :=
  (show List UInt8 from match mode, fullState with
    | .digest, false => [0x41, 0x57, 0x41, 0x56, 0x41, 0x54, 0x53]
    | .digest, true => [0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53]
    | _, _ => [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53]) ++
    [0x48, 0x81, 0xec] ++ immBytes 32 (BitVec.ofNat 32 ((mode.frameSize v keccak fullState) - mode.savedBytes fullState))

def prologueTextOffset (v : Variant) (mode : Mode) (keccak fullState : Bool := false) : Nat :=
  (mode.entry v keccak fullState).entryAddress.toNat - Extracted.textAddress.toNat

theorem prologueCode (v : Variant) (mode : Mode) (keccak fullState : Bool := false) :
    ∀ x ∈ codeRange (mode.entry v keccak fullState).entryAddress (prologueCodeBytes v mode keccak fullState),
      x ∈ Extracted.programImage := by
  have hbound : prologueTextOffset v mode keccak fullState + (pushOffset (mode.pushCount fullState) mode fullState + 7) ≤ Extracted.textBytes.size := by
    cases keccak <;> cases fullState <;> cases mode <;> cases v <;> decide +kernel
  have hbytes : Extracted.textBytes.toListFrom (prologueTextOffset v mode keccak fullState) (pushOffset (mode.pushCount fullState) mode fullState + 7) =
      prologueCodeBytes v mode keccak fullState := by
    cases keccak <;> cases fullState <;> cases mode <;> cases v <;> decide +kernel
  have haddress : Extracted.textAddress + BitVec.ofNat 64 (prologueTextOffset v mode keccak fullState) =
      (mode.entry v keccak fullState).entryAddress := by
    cases keccak <;> cases fullState <;> cases mode <;> cases v <;> rfl
  rw [← haddress]
  exact textSlice_subset_programImage hbound hbytes

theorem pushOffset_succ {n : Nat} {mode : Mode} {fullState : Bool} (h : n < mode.pushCount fullState) :
    pushOffset (n + 1) mode fullState = pushOffset n mode fullState + (encodePushR64 (pushSource n mode fullState)).length := by
  have hcount := pushCount_le_six mode fullState
  have hn : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl <;> cases mode <;> cases fullState <;> first | contradiction | decide

theorem pushSource_length {n : Nat} {mode : Mode} {fullState : Bool} (h : n < mode.pushCount fullState) :
    0 < (encodePushR64 (pushSource n mode fullState)).length ∧
      (encodePushR64 (pushSource n mode fullState)).length < 2^32 := by
  have hcount := pushCount_le_six mode fullState
  have hn : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl <;> cases mode <;> cases fullState <;> first | contradiction | decide

theorem pushedState_rsp (initial : RamState) (n : Nat) (mode : Mode := .plain) (fullState : Bool := false) :
    stackPtr (pushedState initial n mode fullState) = initial.regValue .rsp - BitVec.ofNat 64 (8 * n) := by
  induction n with
  | zero => exact (BitVec.sub_zero _).symm
  | succ n ih =>
    change stackPtr (pushAfter (pushedState initial n mode fullState) (pushSource n mode fullState)) = _
    rw [pushAfter_rsp, pushAddr, ih, Nat.mul_succ, BitVec.ofNat_add, ← BitVec.sub_sub]
    rfl

theorem stack_push_readable_after [Bindings] {initial s : RamState} {v : Variant} {mode : Mode} {keccak fullState : Bool}
    {n : Nat} (h : Invariant initial v mode s keccak fullState)
    (hStack : Stack.Valid initial (mode.entry v keccak fullState).minStackBytes)
    (hBudget : 8 * (n + 1) ≤ (mode.entry v keccak fullState).minStackBytes)
    (hsp : stackPtr s = initial.regValue .rsp - BitVec.ofNat 64 (8 * n)) :
    MemReadable s (pushAddr s) 8 ∧ (pushAddr s).toNat % 4096 + 8 ≤ 4096 := by
  have he : pushAddr s = initial.regValue .rsp - BitVec.ofNat 64 (8 * (n + 1)) := by
    rw [pushAddr, hsp, Nat.mul_succ, BitVec.ofNat_add, ← BitVec.sub_sub]
    rfl
  rw [he]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have hl := stack_sub_low hStack hBudget
    change _ ≤ 2^32
    change _ < 2^32 at hl
    omega
  · intro i hi
    exact h.grows _ (Option.isSome_iff_exists.mpr
      (stack_sub_allocated hStack hBudget (by omega)))
  · rw [stack_sub_toNat hStack.2.2.1 hBudget]
    have ha := hStack.2.2.2
    change (initial.regValue .rsp).toNat % 16 = 8 at ha
    have hu := hStack.2.2.1
    change (mode.entry v keccak fullState).minStackBytes ≤ (initial.regValue .rsp).toNat at hu
    omega

theorem Invariant.push [bindings : Bindings] {initial s : RamState} {v : Variant} {mode : Mode} {keccak fullState : Bool}
    {inputs : Array Input} {split : Nat} {n : Nat} (h : Invariant initial v mode s keccak fullState)
    (hCall : ValidInvocation bindings v mode initial inputs split keccak fullState)
    (hBudget : 8 * (n + 1) ≤ (mode.entry v keccak fullState).minStackBytes)
    (hsp : stackPtr s = initial.regValue .rsp - BitVec.ofNat 64 (8 * n))
    (src : BitVec 4) : Invariant initial v mode (pushAfter s src) keccak fullState := by
  have he : pushAddr s = initial.regValue .rsp - BitVec.ofNat 64 (8 * (n + 1)) := by
    rw [pushAddr, hsp, Nat.mul_succ, BitVec.ofNat_add, ← BitVec.sub_sub]
    rfl
  have hw : ∀ i, i < 8 → ∃ region ∈ writeRegions initial v mode keccak fullState,
      region.Contains (pushAddr s + BitVec.ofNat 64 i).toNat := by
    intro i hi
    refine ⟨Stack.region initial (mode.entry v keccak fullState).minStackBytes,
      stack_mem_writeRegions initial v mode keccak fullState, ?_⟩
    rw [he]
    exact stack_sub_contains hCall.stackAvailable hBudget (by omega)
  have ha := AgreesExcept.afterStep_push s (encodePushR64 src).length
    ((Operand.reg (src.setWidth 5) : Operand 64).read s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (encodePushR64 src).length))
  refine h.of_agreesExcept hCall ?_ ha ?_
  · apply h.ready.of_agreesExcept ha
    apply identityPageTableMemory_memStore_of_avoids s _ _ (writeRegions initial v mode keccak fullState)
      h.ready.memory.tables hw
    intro region hr address hc ht
    exact writeRegions_avoid hCall region hr address hc (.inr ht)
  · intro component hc address hcover
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact hcover.elim
    · obtain ⟨i, hi, rfl⟩ := hcover
      exact hw i hi
    · exact hcover.elim

theorem pushCode_subset (v : Variant) (mode : Mode) (keccak fullState : Bool := false) {n : Nat} (hn : n < mode.pushCount fullState) (p : BitVec 64) :
    ∀ x ∈ codeRange (p + BitVec.ofNat 64 (pushOffset n mode fullState)) (encodePushR64 (pushSource n mode fullState)),
      x ∈ codeRange p (prologueCodeBytes v mode keccak fullState) := by
  apply codeRange_mem_of_drop
  have hcount := pushCount_le_six mode fullState
  have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl <;> cases keccak <;> cases fullState <;> cases mode <;> cases v <;> first | contradiction | decide

theorem pushedState_invariant [bindings : Bindings] {initial : RamState} {v : Variant} {mode : Mode} {keccak fullState : Bool}
    {inputs : Array Input} {split : Nat} (h : Invariant initial v mode initial keccak fullState)
    (hCall : ValidInvocation bindings v mode initial inputs split keccak fullState)
    (hBudget : 48 ≤ (mode.entry v keccak fullState).minStackBytes)
    {n : Nat} (hn : n ≤ mode.pushCount fullState) : Invariant initial v mode (pushedState initial n mode fullState) keccak fullState := by
  have hcount := pushCount_le_six mode fullState
  induction n with
  | zero => exact h
  | succ n ih =>
    exact (ih (by omega)).push hCall (by omega) (pushedState_rsp initial n mode fullState) (pushSource n mode fullState)

theorem pushedState_rip [bindings : Bindings] {initial : RamState} {v : Variant} {mode : Mode} {keccak fullState : Bool}
    {inputs : Array Input} {split : Nat} (h : Invariant initial v mode initial keccak fullState)
    (hCall : ValidInvocation bindings v mode initial inputs split keccak fullState)
    (hBudget : 48 ≤ (mode.entry v keccak fullState).minStackBytes)
    {n : Nat} (hn : n ≤ mode.pushCount fullState) :
    (pushedState initial n mode fullState).RIP = (mode.entry v keccak fullState).entryAddress + BitVec.ofNat 64 (pushOffset n mode fullState) := by
  induction n with
  | zero =>
    cases mode <;> cases fullState <;>
      simpa only [pushedState, pushOffset, Nat.mul_zero, Nat.zero_min,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hCall.atEntryPoint
  | succ n ih =>
    change (pushAfter (pushedState initial n mode fullState) (pushSource n mode fullState)).RIP = _
    rw [show (pushAfter (pushedState initial n mode fullState) (pushSource n mode fullState)).RIP =
      BitVec.add (pushedState initial n mode fullState).RIP
        (BitVec.ofNat 64 (encodePushR64 (pushSource n mode fullState)).length) from
      afterStep_push_rip (pushedState_invariant h hCall hBudget (by omega)).ready _ _ _]
    rw [ih (by omega), pushOffset_succ (by omega), BitVec.ofNat_add]
    exact BitVec.add_assoc _ _ _

theorem pushedState_boundary_ne {initial : RamState} {budget n : Nat} {mode : Mode} {fullState : Bool}
    (hStack : Stack.Valid initial budget) (hBudget : 8 * (n + 1) ≤ budget) :
    (pushedState initial (n + 1) mode fullState).GPR[4] ≠ (returnBoundary initial).rsp := by
  change stackPtr (pushedState initial (n + 1) mode fullState) ≠ initial.regValue .rsp + 8
  rw [pushedState_rsp _ _ mode fullState]
  intro he
  have ht := congrArg BitVec.toNat he
  rw [stack_sub_toNat hStack.2.2.1 hBudget, BitVec.toNat_add] at ht
  have hl := hStack.1
  have hu := hStack.2.2.1
  change budget ≤ (initial.regValue .rsp).toNat at hu
  simp only [Stack.region, Stack.returnAddressBytes, MemoryRegion.Bounded,
    userAddressLimit] at hl
  change (initial.regValue .rsp).toNat - 8 * (n + 1) =
    ((initial.regValue .rsp).toNat + 8) % 2^64 at ht
  omega

theorem pushedState_advances [bindings : Bindings] {initial : RamState} {v : Variant} {mode : Mode} {keccak fullState : Bool}
    {inputs : Array Input} {split : Nat} (h : Invariant initial v mode initial keccak fullState)
    (hCall : ValidInvocation bindings v mode initial inputs split keccak fullState)
    (hBudget : 48 ≤ (mode.entry v keccak fullState).minStackBytes)
    (hCode : ∀ x ∈ codeRange (mode.entry v keccak fullState).entryAddress (prologueCodeBytes v mode keccak fullState),
      x ∈ Extracted.programImage)
    {n : Nat} (hn : n ≤ mode.pushCount fullState) :
    Advances (returnBoundary initial) n initial (pushedState initial n mode fullState) := by
  have hcount := pushCount_le_six mode fullState
  induction n with
  | zero => exact (advances_zero _ _ _).mpr rfl
  | succ n ih =>
    have hInv := pushedState_invariant h hCall hBudget (by omega : n ≤ mode.pushCount fullState)
    have hRip := pushedState_rip h hCall hBudget (by omega : n ≤ mode.pushCount fullState)
    have hBytes := hInv.code.mono
      (fun x hx ↦ hCode x (pushCode_subset v mode keccak fullState (n := n) (by omega) _ x hx))
    have hMem := stack_push_readable_after hInv hCall.stackAvailable
      (by omega : 8 * (n + 1) ≤ (mode.entry v keccak fullState).minStackBytes) (pushedState_rsp initial n mode fullState)
    have hStep := push_r64_step_of_register_readable (pushedState initial n mode fullState) hInv.ready
      (pushSource n mode fullState) (hRip ▸ hBytes.bytesAt)
      (hRip ▸ hBytes.low (pushSource_length (by omega)).1 (pushSource_length (by omega)).2)
      hMem.1 hMem.2
    exact (ih (by omega)).trans (Advances.of_step hStep
      (.inr (pushedState_boundary_ne hCall.stackAvailable (by omega))))

def allocateFrame (s : RamState) (v : Variant) (mode : Mode) (keccak fullState : Bool := false) : RamState :=
  afterStep s 7 fun t ↦ writeOutputs t (.reg 4)
    (subSpec ((Operand.reg 4 : Operand 64).read t) (BitVec.ofNat 64 ((mode.frameSize v keccak fullState) - mode.savedBytes fullState)))
    0 (BitVec.add s.RIP 7)

def prologueState (initial : RamState) (v : Variant) (mode : Mode) (keccak fullState : Bool := false) : RamState :=
  allocateFrame (pushedState initial (mode.pushCount fullState) mode fullState) v mode keccak fullState

theorem allocateFrame_rsp (s : RamState) (v : Variant) (mode : Mode) (keccak fullState : Bool := false) :
    stackPtr (allocateFrame s v mode keccak fullState) = stackPtr s - BitVec.ofNat 64 ((mode.frameSize v keccak fullState) - mode.savedBytes fullState) := by
  change (Operand.reg 4 : Operand 64).read (allocateFrame s v mode keccak fullState) = _
  rw [allocateFrame, Operand.read_afterStep, Operand.read_writeOutputs_self]
  rfl

theorem prologueState_rsp (initial : RamState) (v : Variant) (mode : Mode) (keccak fullState : Bool := false) :
    stackPtr (prologueState initial v mode keccak fullState) = frameBase initial v mode keccak fullState := by
  rw [prologueState, allocateFrame_rsp _ _ _ keccak fullState, pushedState_rsp _ _ mode fullState, BitVec.sub_sub]
  cases keccak <;> cases fullState <;> cases mode <;> cases v <;> rfl

theorem Invariant.allocate [bindings : Bindings] {initial s : RamState} {v : Variant} {mode : Mode} {keccak fullState : Bool}
    {inputs : Array Input} {split : Nat} (h : Invariant initial v mode s keccak fullState)
    (hCall : ValidInvocation bindings v mode initial inputs split keccak fullState) :
    Invariant initial v mode (allocateFrame s v mode keccak fullState) keccak fullState := by
  refine h.of_agreesExcept hCall
    (ReadyToStep.afterStep_writeOutputs h.ready 7 4 _ 0 _)
    (AgreesExcept.afterStep_writeOutputs s 7 4 _ 0 _) ?_
  intro c hc address hcov
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> exact hcov.elim

theorem prologueState_invariant [bindings : Bindings] {initial : RamState} {v : Variant}
    {mode : Mode} {keccak fullState : Bool} {inputs : Array Input} {split : Nat} (h : Invariant initial v mode initial keccak fullState)
    (hCall : ValidInvocation bindings v mode initial inputs split keccak fullState)
    (hBudget : 48 ≤ (mode.entry v keccak fullState).minStackBytes) :
    Invariant initial v mode (prologueState initial v mode keccak fullState) keccak fullState :=
  (pushedState_invariant h hCall hBudget (Nat.le_refl (mode.pushCount fullState))).allocate hCall

theorem allocateFrame_rip [Bindings] {s : RamState} {v : Variant} {mode : Mode} {keccak fullState : Bool} (h : ReadyToStep s) :
    (allocateFrame s v mode keccak fullState).RIP = BitVec.add s.RIP 7 :=
  afterStep_writeOutputs_rip h 7 _ _ 0 _

theorem prologueState_rip [bindings : Bindings] {initial : RamState} {v : Variant} {mode : Mode} {keccak fullState : Bool}
    {inputs : Array Input} {split : Nat} (h : Invariant initial v mode initial keccak fullState)
    (hCall : ValidInvocation bindings v mode initial inputs split keccak fullState)
    (hBudget : 48 ≤ (mode.entry v keccak fullState).minStackBytes) :
    (prologueState initial v mode keccak fullState).RIP = (mode.entry v keccak fullState).entryAddress + BitVec.ofNat 64 (pushOffset (mode.pushCount fullState) mode fullState + 7) := by
  rw [prologueState, allocateFrame_rip
    (pushedState_invariant h hCall hBudget (Nat.le_refl (mode.pushCount fullState))).ready,
    pushedState_rip h hCall hBudget (Nat.le_refl (mode.pushCount fullState)), BitVec.ofNat_add]
  exact BitVec.add_assoc _ _ _

theorem prologueState_step [bindings : Bindings] {initial : RamState} {v : Variant} {mode : Mode} {keccak fullState : Bool}
    {inputs : Array Input} {split : Nat} (h : Invariant initial v mode initial keccak fullState)
    (hCall : ValidInvocation bindings v mode initial inputs split keccak fullState)
    (hBudget : 48 ≤ (mode.entry v keccak fullState).minStackBytes)
    (hCode : ∀ x ∈ codeRange (mode.entry v keccak fullState).entryAddress (prologueCodeBytes v mode keccak fullState),
      x ∈ Extracted.programImage) :
    Machine.step (pushedState initial (mode.pushCount fullState) mode fullState) = some (.next (prologueState initial v mode keccak fullState)) := by
  have hp := pushedState_invariant h hCall hBudget (Nat.le_refl (mode.pushCount fullState))
  have hRip := pushedState_rip h hCall hBudget (Nat.le_refl (mode.pushCount fullState))
  have hs : ∀ x ∈ codeRange ((mode.entry v keccak fullState).entryAddress + BitVec.ofNat 64 (pushOffset (mode.pushCount fullState) mode fullState))
      (0x48 :: 0x81 :: 0xec :: immBytes 32 (BitVec.ofNat 32 ((mode.frameSize v keccak fullState) - mode.savedBytes fullState))),
      x ∈ Extracted.programImage := by
    intro x hx
    exact hCode x (codeRange_mem_of_drop (pushOffset (mode.pushCount fullState) mode fullState) (by cases keccak <;> cases fullState <;> cases mode <;> cases v <;> decide) x hx)
  have hc := hp.code.mono hs
  have hc' : CodeIn (codeRange (pushedState initial (mode.pushCount fullState) mode fullState).RIP
      (0x48 :: 0x81 :: 0xec :: immBytes 32 (BitVec.ofNat 32 ((mode.frameSize v keccak fullState) - mode.savedBytes fullState))))
      (pushedState initial (mode.pushCount fullState) mode fullState) := hRip ▸ hc
  have hstep := sub_r64_imm32_step _ hp.ready 0x48 0xec
    (BitVec.ofNat 32 ((mode.frameSize v keccak fullState) - mode.savedBytes fullState))
    (by unfold RexWPrefix; decide) (by decide) (by decide) hc'.bytesAt
    (hc'.low (by simp) (by simp))
  cases keccak <;> cases fullState <;> cases mode <;> cases v <;> exact hstep

theorem prologueState_advances [bindings : Bindings] {initial : RamState} {v : Variant}
    {mode : Mode} {keccak fullState : Bool} {inputs : Array Input} {split : Nat} (h : Invariant initial v mode initial keccak fullState)
    (hCall : ValidInvocation bindings v mode initial inputs split keccak fullState) :
    Advances (returnBoundary initial) (mode.pushCount fullState + 1) initial (prologueState initial v mode keccak fullState) := by
  have hsize : 48 ≤ (mode.frameSize v keccak fullState) := by cases keccak <;> cases fullState <;> cases mode <;> cases v <;> decide
  have hBudget : (mode.frameSize v keccak fullState) ≤ (mode.entry v keccak fullState).minStackBytes := by
    rw [Mode.stackBudget mode v keccak fullState]
    omega
  have hCode := prologueCode v mode keccak fullState
  change Advances (returnBoundary initial) (mode.pushCount fullState + 1) initial (prologueState initial v mode keccak fullState)
  apply (pushedState_advances h hCall (by omega) hCode (Nat.le_refl (mode.pushCount fullState))).trans
  apply Advances.of_step (prologueState_step h hCall (by omega) hCode)
  right
  change stackPtr (prologueState initial v mode keccak fullState) ≠ initial.regValue .rsp + 8
  rw [prologueState_rsp initial v mode keccak fullState]
  intro he
  have ht := congrArg BitVec.toNat he
  change (initial.regValue .rsp - BitVec.ofNat 64 (mode.frameSize v keccak fullState)).toNat = _ at ht
  rw [stack_sub_toNat hCall.stackAvailable.2.2.1 hBudget, BitVec.toNat_add] at ht
  have hl := hCall.stackAvailable.1
  have hu := hCall.stackAvailable.2.2.1
  change (mode.entry v keccak fullState).minStackBytes ≤ (initial.regValue .rsp).toNat at hu
  simp only [Stack.region, Stack.returnAddressBytes, MemoryRegion.Bounded,
    userAddressLimit] at hl
  change (initial.regValue .rsp).toNat - (mode.frameSize v keccak fullState) =
    ((initial.regValue .rsp).toNat + 8) % 2^64 at ht
  omega

theorem pushedState_register (initial : RamState) (n : Nat) (r : BitVec 5) (hr : r ≠ 4) (mode : Mode := .plain) (fullState : Bool := false) :
    (Operand.reg r : Operand 64).read (pushedState initial n mode fullState) =
      (Operand.reg r : Operand 64).read initial := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have ha := AgreesExcept.afterStep_push (pushedState initial n mode fullState)
      (encodePushR64 (pushSource n mode fullState)).length
      ((Operand.reg ((pushSource n mode fullState).setWidth 5) : Operand 64).read (pushedState initial n mode fullState))
      (BitVec.add (pushedState initial n mode fullState).RIP
        (BitVec.ofNat 64 (encodePushR64 (pushSource n mode fullState)).length))
    exact (ha.read (by simpa only [List.mem_cons, Component.reg.injEq,
      List.not_mem_nil, or_false, reduceCtorEq, or_false] using hr)).trans ih

theorem prologueState_register (initial : RamState) (v : Variant) (mode : Mode) (r : BitVec 5) (hr : r ≠ 4) (keccak fullState : Bool := false) :
    (Operand.reg r : Operand 64).read (prologueState initial v mode keccak fullState) =
      (Operand.reg r : Operand 64).read initial := by
  have ha := AgreesExcept.afterStep_writeOutputs (pushedState initial (mode.pushCount fullState) mode fullState) 7 4
    (fun t ↦ subSpec ((Operand.reg 4 : Operand 64).read t)
      (BitVec.ofNat 64 ((mode.frameSize v keccak fullState) - mode.savedBytes fullState))) 0
    (BitVec.add (pushedState initial (mode.pushCount fullState) mode fullState).RIP 7)
  exact (ha.read (by simpa only [List.mem_cons, Component.reg.injEq,
    List.not_mem_nil, or_false, reduceCtorEq, or_false] using hr)).trans
    (pushedState_register initial (mode.pushCount fullState) r hr mode fullState)

def pushedBytes (initial : RamState) (n : Nat) (mode : Mode := .plain)
    (fullState : Bool := false) (i : Nat) : UInt8 :=
  match n with
  | 0 => memByte initial.external (stackPtr initial + BitVec.ofNat 64 i)
  | n + 1 => if i < 8 then
      storedByte ((Operand.reg ((pushSource n mode fullState).setWidth 5) : Operand 64).read initial) i
    else pushedBytes initial n mode fullState (i - 8)

theorem pushSource_ne_rsp (n : Nat) (mode : Mode := .plain) (fullState : Bool := false) : (pushSource n mode fullState).setWidth 5 ≠ 4 := by
  cases mode <;> cases fullState <;> unfold pushSource <;> split <;> decide

theorem pushedState_bytes {initial : RamState} {budget n : Nat} {mode : Mode} {fullState : Bool}
    (hStack : Stack.Valid initial budget) (hn : n ≤ mode.pushCount fullState) :
    Bytes (pushedState initial n mode fullState).external (stackPtr (pushedState initial n mode fullState)) (8 * n + 8)
      (pushedBytes initial n mode fullState) := by
  have hcount := pushCount_le_six mode fullState
  induction n with
  | zero => exact Bytes.of_isSome (stack_return_readable hStack).mem
  | succ n ih =>
    have hp := (ih (by omega)).pushAfter (pushSource n mode fullState) (by omega)
    rw [show 8 + (8 * n + 8) = 8 * (n + 1) + 8 by omega] at hp
    apply hp.congr
    intro i hi
    change (if i < 8 then _ else _) = (if i < 8 then _ else _)
    rw [pushedState_register initial n _ (pushSource_ne_rsp n mode fullState) mode fullState]

theorem savedFrame_slot (initial : RamState) (mode : Mode) (fullState : Bool) (i : Fin (mode.pushCount fullState)) :
    initial.regValue .rsp - BitVec.ofNat 64 (mode.savedBytes fullState) + BitVec.ofNat 64 (8 * i.val) =
      stackPtr (pushedState initial (mode.pushCount fullState) mode fullState) + BitVec.ofNat 64 (8 * i.val) := by
  rw [pushedState_rsp _ _ mode fullState]
  rfl

theorem pushedBytes_saved (initial : RamState) (mode : Mode) (fullState : Bool) (i : Fin (mode.pushCount fullState)) (j : Nat) (hj : j < 8) :
    pushedBytes initial (mode.pushCount fullState) mode fullState (8 * i.val + j) = storedByte (initial.regValue (mode.savedRegisters fullState)[i]) j := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases mode <;> cases fullState
  all_goals first | change Fin 4 at i | change Fin 5 at i | change Fin 6 at i
  all_goals finite_cases i <;> rfl

theorem pushedState_savedFrame {initial : RamState} {budget : Nat} {mode : Mode} {fullState : Bool}
    (hStack : Stack.Valid initial budget) : SavedFrame initial (pushedState initial (mode.pushCount fullState) mode fullState) mode fullState := by
  have hb := pushedState_bytes hStack (Nat.le_refl (mode.pushCount fullState))
  constructor
  · change ∀ i : Fin (mode.pushCount fullState), memLoad (pushedState initial (mode.pushCount fullState) mode fullState).external
      (initial.regValue .rsp - BitVec.ofNat 64 (mode.savedBytes fullState) + BitVec.ofNat 64 (8 * i.val)) 64 =
      initial.regValue (mode.savedRegisters fullState)[i]
    intro i
    rw [savedFrame_slot initial mode fullState]
    apply Bytes.memLoad (hn := by decide) (h128 := by decide)
    exact ((hb.sub (8 * i.val) 8 (by have := i.isLt; omega)).congr
      (fun j hj ↦ pushedBytes_saved initial mode fullState i j hj))
  · change memLoad (pushedState initial (mode.pushCount fullState) mode fullState).external (stackPtr initial) 64 =
      memLoad initial.external (stackPtr initial) 64
    have he : stackPtr (pushedState initial (mode.pushCount fullState) mode fullState) + BitVec.ofNat 64 (mode.savedBytes fullState) = stackPtr initial := by
      rw [pushedState_rsp _ _ mode fullState]
      exact BitVec.sub_add_cancel _ _
    have ht := hb.sub (mode.savedBytes fullState) 8 (by unfold Mode.savedBytes; omega)
    rw [he] at ht
    apply memLoad_congr
    intro i hi
    have hbi := ht i hi
    have hv : pushedBytes initial (mode.pushCount fullState) mode fullState (mode.savedBytes fullState + i) =
        memByte initial.external (stackPtr initial + BitVec.ofNat 64 i) := by
      cases mode <;> cases fullState <;> simp +arith [pushedBytes, Mode.savedBytes, Mode.pushCount]
    dsimp only at hbi
    rw [hv] at hbi
    change ((pushedState initial (mode.pushCount fullState) mode fullState).external[stackPtr initial + BitVec.ofNat 64 i]?).getD 0 = _
    rw [hbi]
    rfl

theorem SavedFrame.of_external_eq {initial s t : RamState} {mode : Mode} {fullState : Bool}
    (h : SavedFrame initial s mode fullState) (he : t.external = s.external) :
    SavedFrame initial t mode fullState := by
  constructor
  · intro i
    change memLoad t.external _ 64 = _
    rw [he]
    exact h.saved i
  · change memLoad t.external _ 64 = _
    rw [he]
    exact h.returnSlot

theorem allocateFrame_external (s : RamState) (v : Variant) (mode : Mode) (keccak fullState : Bool := false) :
    (allocateFrame s v mode keccak fullState).external = s.external := rfl

theorem prologueState_savedFrame {initial : RamState} {budget : Nat} (v : Variant) (mode : Mode)
    (hStack : Stack.Valid initial budget) (keccak fullState : Bool := false) :
    SavedFrame initial (prologueState initial v mode keccak fullState) mode fullState := by
  have hs := (pushedState_savedFrame hStack).of_external_eq
    (allocateFrame_external (pushedState initial (mode.pushCount fullState) mode fullState) v mode keccak fullState)
  exact hs

theorem entry_prologue [bindings : Bindings] {initial : RamState} {v : Variant} {mode : Mode} {keccak fullState : Bool}
    {inputs : Array Input} {split : Nat}
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hEnvironment : MachineRamUnitStrideDecodable bindings initial)
    (hCall : ValidInvocation bindings v mode initial inputs split keccak fullState) :
    nearReturn64Boundary initial = .ok (returnBoundary initial) ∧
    Advances (returnBoundary initial) (mode.pushCount fullState + 1) initial (prologueState initial v mode keccak fullState) ∧
    Invariant initial v mode (prologueState initial v mode keccak fullState) keccak fullState ∧
    SavedFrame initial (prologueState initial v mode keccak fullState) mode fullState := by
  have h := Invariant.initial hMachine hEnvironment hCall
  have hPush : 48 ≤ (mode.entry v keccak fullState).minStackBytes := by
    rw [Mode.stackBudget mode v keccak fullState]
    omega
  exact ⟨nearReturn64Boundary_eq initial h.ready.dataReady h.ready.cpu.ss
      (stack_return_readable hCall.stackAvailable),
    prologueState_advances h hCall,
    prologueState_invariant h hCall hPush, prologueState_savedFrame v mode hCall.stackAvailable keccak fullState⟩

end Sha3.Proofs.Wrapper
