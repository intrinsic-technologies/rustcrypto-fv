import Sha3.Proofs.Wrapper.Setup.Basic
import Sha3.Proofs.Memset
import Sha3.Proofs.Calls
import Sha3.Proofs.Stores.Frame

namespace Sha3.Proofs.Wrapper

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

theorem statePointer_sub (initial : RamState) (v : Variant) (mode : Mode) (keccak : Bool := false) (fullState : Bool := false) :
    statePointer initial v mode keccak fullState =
      initial.regValue .rsp - BitVec.ofNat 64 ((mode.frameSize v keccak fullState) - (mode.stateOffset v keccak fullState)) := by
  cases keccak <;> cases fullState <;> cases mode <;> cases v <;> simp [statePointer, frameBase, Mode.frameSize, Mode.stateOffset,
    BitVec.sub_eq_add_neg, BitVec.add_assoc]

theorem frameBase_sub_eight (initial : RamState) (v : Variant) (mode : Mode) (keccak : Bool := false) (fullState : Bool := false) :
    frameBase initial v mode keccak fullState - (8 : BitVec 64) =
      initial.regValue .rsp - BitVec.ofNat 64 ((mode.frameSize v keccak fullState) + 8) := by
  rw [frameBase, BitVec.sub_sub, BitVec.ofNat_add]
  rfl

private theorem stackReadable [bindings : Bindings] {initial s : RamState}
    {v : Variant} {mode : Mode} {keccak fullState : Bool}
    (inv : Invariant initial v mode s keccak fullState) (hStack : Stack.Valid initial (mode.entry v keccak fullState).minStackBytes)
    {offset count : Nat} (hbudget : offset ≤ (mode.entry v keccak fullState).minStackBytes)
    (hcount : count ≤ offset) :
    MemReadable s (initial.regValue .rsp - BitVec.ofNat 64 offset) count := by
  have hlow := stack_sub_low hStack hbudget
  change (initial.regValue .rsp - BitVec.ofNat 64 offset).toNat + offset < 2 ^ 32 at hlow
  refine ⟨by omega, ?_⟩
  intro i hi
  obtain ⟨v, hv⟩ := stack_sub_allocated hStack hbudget (by omega : i < offset)
  exact inv.grows _ (by rw [hv]; rfl)

theorem memsetPointer_read {s : RamState} (loaded : ProgramLoaded s) :
    (Operand.mem 0x200188 : Operand 64).read s = 0x106a20 := by
  have hb : ∀ i : Fin 8,
      s.external[(0x200188 : BitVec 64) + BitVec.ofNat 64 i.val]? =
        some (storedByte (0x106a20 : BitVec 64) i.val) := by
    intro i
    exact programLoaded_fetchByte loaded
      ((by decide +kernel : ∀ i : Fin 8,
        Extracted.programSections.fetchByte ((0x200188 : BitVec 64) + BitVec.ofNat 64 i.val) =
          some (storedByte (0x106a20 : BitVec 64) i.val)) i)
  change memLoad s.external 0x200188 64 = _
  rw [← memLoad_memStore (∅ : Ram) (0x200188 : BitVec 64) (by decide) (by decide)
    (0x106a20 : BitVec 64)]
  apply memLoad_congr
  intro i hi
  simp only [memByte, PhysicalMemory.read, hb ⟨i, hi⟩,
    memStore_getElem?_self _ _ _ (by decide) i hi]

private theorem memsetPointer_readable {s : RamState} (loaded : ProgramLoaded s) :
    MemReadable s 0x200188 8 := by
  refine ⟨by decide +kernel, ?_⟩
  intro i hi
  have hb := programLoaded_fetchByte loaded
    ((by decide +kernel : ∀ i : Fin 8,
      Extracted.programSections.fetchByte ((0x200188 : BitVec 64) + BitVec.ofNat 64 i.val) =
        some (storedByte (0x106a20 : BitVec 64) i.val)) ⟨i, hi⟩)
  rw [hb]
  rfl

private theorem callWrites [bindings : Bindings] {initial s : RamState} {v : Variant} {mode : Mode} {keccak fullState : Bool}
    {inputs : Array Input} {split : Nat}
    (hCall : ValidInvocation bindings v mode initial inputs split keccak fullState)
    (hbudget : (mode.frameSize v keccak fullState) + 8 ≤ (mode.entry v keccak fullState).minStackBytes)
    (sp : stackPtr s = frameBase initial v mode keccak fullState) :
    ∀ i, i < 8 → ∃ region ∈ writeRegions initial v mode keccak fullState,
      region.Contains (pushAddr s + BitVec.ofNat 64 i).toNat := by
  intro i hi
  refine ⟨Stack.region initial (mode.entry v keccak fullState).minStackBytes,
      stack_mem_writeRegions initial v mode keccak fullState, ?_⟩
  rw [pushAddr, sp, frameBase_sub_eight (keccak := keccak) (fullState := fullState)]
  exact stack_sub_contains (offset := (mode.frameSize v keccak fullState) + 8) hCall.stackAvailable hbudget (by omega)

theorem initial_memset_call_form [bindings : Bindings] {initial s : RamState} {v : Variant} {mode : Mode} {keccak fullState : Bool}
    {inputs : Array Input} {split : Nat}
    (boundary : ReturnBoundary) (p : BitVec 64) (disp : BitVec 32) (regCall : Bool)
    (hCall : ValidInvocation bindings v mode initial inputs split keccak fullState)
    (hbudget : (mode.frameSize v keccak fullState) + 8 ≤ (mode.entry v keccak fullState).minStackBytes)
    (image : ImageAt p (if regCall then [0x41, 0xff, 0xd5] else encodeCallM64 (.rip disp)))
    (target : if regCall then (Operand.reg 13 : Operand 64).read s = 0x106a20
      else (p + (6 : BitVec 64)) + disp.signExtend 64 = 0x200188)
    (inv : Invariant initial v mode s keccak fullState) (ip : s.RIP = p)
    (sp : stackPtr s = frameBase initial v mode keccak fullState)
    (inside : frameBase initial v mode keccak fullState - (8 : BitVec 64) ≠ boundary.rsp) :
    ∃ t, Advances boundary 1 s t ∧ Invariant initial v mode t keccak fullState ∧
      t.RIP = 0x106a20 ∧ stackPtr t = frameBase initial v mode keccak fullState - (8 : BitVec 64) ∧
      stackTop t = p + (if regCall then 3 else 6 : BitVec 64) ∧
      AgreesExcept [.reg 4, .mem (frameBase initial v mode keccak fullState - (8 : BitVec 64)) 8, .rip] s t := by
  have hp : pushAddr s = frameBase initial v mode keccak fullState - (8 : BitVec 64) := by rw [pushAddr, sp]
  have hr : MemReadable s (pushAddr s) 8 := by
    rw [hp, frameBase_sub_eight (keccak := keccak) (fullState := fullState)]
    exact stackReadable inv hCall.stackAvailable hbudget (by omega)
  have hpage : (pushAddr s).toNat % 4096 + 8 ≤ 4096 := by
    rw [hp, frameBase_sub_eight (keccak := keccak) (fullState := fullState)]
    change (initial.regValue .rsp - BitVec.ofNat 64 ((mode.frameSize v keccak fullState) + 8)).toNat % 4096 + 8 ≤ 4096
    rw [stack_sub_toNat hCall.stackAvailable.2.2.1 hbudget]
    have hu := hCall.stackAvailable.2.2.1
    have halign := hCall.stackAvailable.2.2.2
    change (mode.entry v keccak fullState).minStackBytes ≤ (initial.regValue .rsp).toNat at hu
    change (initial.regValue .rsp).toNat % 16 = 8 at halign
    cases keccak <;> cases fullState <;> cases mode <;> cases v <;> simp only [Mode.frameSize, Bool.false_eq_true, ↓reduceIte] at * <;> omega
  have result : ∃ t, Machine.step s = some (.next t) ∧ ReadyToStep t ∧
      (callEffect (fun _ ↦ (0x106a20 : BitVec 64))
        (p + (if regCall then 3 else 6 : BitVec 64)) s).Holds s t := by
    cases regCall with
    | false =>
      have ha (u : RamState) : (AddrMode.rip disp).addr u (p + 6) = 0x200188 := target
      have ht : callMemPtr p (.rip disp) s = 0x106a20 := by
        change (Operand.mem ((AddrMode.rip disp).addr s (p + 6)) : Operand 64).read s = _
        rw [ha]
        exact memsetPointer_read inv.loaded
      have step := call_m64_rip_effect_step_of_readable
        (pre := fun u ↦ u = s) (p := p) (fun _ ↦ writeRegions initial v mode keccak fullState)
        (by rintro u rfl; exact callWrites hCall hbudget sp)
        (by
          rintro u rfl region hregion address hcontains htables
          exact writeRegions_avoid hCall region hregion address hcontains (.inr htables))
        disp (by rintro u rfl; exact ⟨ip, hr⟩) (by rintro u rfl; exact hpage)
        (by rintro u rfl; rw [ha]; exact memsetPointer_readable inv.loaded)
        (by rintro u rfl; rw [ht]; decide +kernel)
      obtain ⟨t, hs, hr, he⟩ := step s inv.ready (image.code inv.loaded) rfl
      exact ⟨t, hs, hr, by simpa only [callEffect, pushEffect, ht, Bool.false_eq_true, ↓reduceIte] using he⟩
    | true =>
      have ht : (Operand.reg 13 : Operand 64).read s = 0x106a20 := target
      have step := call_effect_step_of_avoids (pre := fun u ↦ u = s)
        (p := p) (bytes := [0x41, 0xff, 0xd5]) (len := 3) false
        (fun _ ↦ (0x106a20 : BitVec 64))
        (fun _ ↦ writeRegions initial v mode keccak fullState)
        (by rintro u rfl; exact callWrites hCall hbudget sp)
        (by
          rintro u rfl region hregion address hcontains htables
          exact writeRegions_avoid hCall region hregion address hcontains (.inr htables))
        (by
          rintro u ready code hu
          subst u
          have hrex : RexPrefix (0x41 : UInt8).toBitVec := by unfold RexPrefix; decide +kernel
          have hs := call_r64_step_of_readable s ready [0x41]
            (by simpa using hrex.scanPrefix) (by decide)
            (by rw [scanContext_rex _ _ hrex]; rfl)
            (by rw [scanContext_rex _ _ hrex]; rfl)
            (by rw [scanContext_rex _ _ hrex]; rfl)
            0xd5 (by decide) (by decide)
            (ip.symm ▸ code.bytesAt) (ip.symm ▸ code.low (by decide) (by decide))
            (by rw [scanContext_rex _ _ hrex]; change ((Operand.reg 13 : Operand 64).read s).toNat < 2^32; rw [target]; decide)
            hr hpage
          simp only [scanContext_rex _ _ hrex] at hs
          change Machine.step s = some (.next (afterStep s 3 fun t ↦
            callState (callFrom false t (BitVec.add s.RIP (BitVec.ofNat 64 3))) (BitVec.add s.RIP (BitVec.ofNat 64 3))
              ((Operand.reg 13 : Operand 64).read s))) at hs
          rw [ip, ht] at hs
          exact hs)
      exact step s inv.ready (image.code inv.loaded) rfl
  obtain ⟨t, hstep, hready, effect⟩ := result
  have frame :
      AgreesExcept [.reg 4, .mem (frameBase initial v mode keccak fullState - (8 : BitVec 64)) 8, .rip] s t := by
    simpa only [pushEffect_components, hp] using effect.agrees
  have hsp : stackPtr t = frameBase initial v mode keccak fullState - (8 : BitVec 64) :=
    effect.writes.1.trans hp
  refine ⟨t, Advances.of_step hstep (.inr (by
      change stackPtr t ≠ boundary.rsp
      rw [hsp]
      exact inside)),
    inv.of_agreesExcept hCall hready frame ?_, effect.rip, hsp,
    (callEffect_stack effect).1, frame⟩
  intro c hc address hcover
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> try exact hcover.elim
  obtain ⟨i, hi, rfl⟩ := hcover
  rw [← hp]
  exact callWrites hCall hbudget sp i hi

theorem initial_memset_call [bindings : Bindings] {initial s : RamState} {v : Variant} {mode : Mode} {keccak fullState : Bool}
    {inputs : Array Input} {split : Nat}
    (boundary : ReturnBoundary) (p : BitVec 64) (disp : BitVec 32)
    (hCall : ValidInvocation bindings v mode initial inputs split keccak fullState)
    (hbudget : (mode.frameSize v keccak fullState) + 8 ≤ (mode.entry v keccak fullState).minStackBytes)
    (image : ImageAt p (encodeCallM64 (.rip disp)))
    (target : (p + (6 : BitVec 64)) + disp.signExtend 64 = 0x200188)
    (inv : Invariant initial v mode s keccak fullState) (ip : s.RIP = p)
    (sp : stackPtr s = frameBase initial v mode keccak fullState)
    (inside : frameBase initial v mode keccak fullState - (8 : BitVec 64) ≠ boundary.rsp) :
    ∃ t, Advances boundary 1 s t ∧ Invariant initial v mode t keccak fullState ∧
      t.RIP = 0x106a20 ∧ stackPtr t = frameBase initial v mode keccak fullState - (8 : BitVec 64) ∧
      stackTop t = p + (6 : BitVec 64) ∧
      AgreesExcept [.reg 4, .mem (frameBase initial v mode keccak fullState - (8 : BitVec 64)) 8, .rip] s t := by
  exact initial_memset_call_form boundary p disp false hCall hbudget image target inv ip sp inside

theorem readMem_agrees {s t : RamState} {cs : List Component} {address : BitVec 64}
    (ha : AgreesExcept cs s t)
    (safe : ∀ i, i < 8 → ∀ c ∈ cs, ¬ c.Covers (address + BitVec.ofNat 64 i)) :
    (Operand.mem address : Operand 64).read t = (Operand.mem address : Operand 64).read s := by
  apply memLoad_congr
  intro i hi
  simp only [memByte, PhysicalMemory.read, ha.byte (safe i hi)]

theorem SavedFrame.of_localFrame {initial s t : RamState} {v : Variant} {mode : Mode} {keccak fullState : Bool} {cs : List Component}
    (saved : SavedFrame initial s mode fullState) (ha : AgreesExcept cs s t)
    (localFrame : ∀ c ∈ cs, ∀ address, c.Covers address →
      (Component.mem (frameBase initial v mode keccak fullState - (8 : BitVec 64))
        ((mode.frameSize v keccak fullState) - (8 * mode.pushCount fullState - 8))).Covers address) :
    SavedFrame initial t mode fullState := by
  have keep (i : Fin (mode.pushCount fullState + 1)) :
      (Operand.mem (initial.regValue .rsp - BitVec.ofNat 64 (8 * mode.pushCount fullState) + BitVec.ofNat 64 (8 * i.val)) :
        Operand 64).read t =
      (Operand.mem (initial.regValue .rsp - BitVec.ofNat 64 (8 * mode.pushCount fullState) + BitVec.ofNat 64 (8 * i.val)) :
        Operand 64).read s := by
    apply readMem_agrees ha
    intro j hj c hc hcover
    obtain ⟨k, hk, he⟩ := localFrame c hc _ hcover
    have apart : OffsetsApart (-BitVec.ofNat 64 ((mode.frameSize v keccak fullState) + 8))
        ((mode.frameSize v keccak fullState) - (8 * mode.pushCount fullState - 8)) (-BitVec.ofNat 64 (8 * mode.pushCount fullState) + BitVec.ofNat 64 (8 * i.val)) 8 := by
      exact (by
        cases keccak <;> cases fullState <;> cases mode <;> cases v <;> unfold Mode.frameSize Mode.pushCount OffsetsApart <;> decide +kernel :
        ∀ i : Fin (mode.pushCount fullState + 1), OffsetsApart (-BitVec.ofNat 64 ((mode.frameSize v keccak fullState) + 8))
          ((mode.frameSize v keccak fullState) - (8 * mode.pushCount fullState - 8)) (-BitVec.ofNat 64 (8 * mode.pushCount fullState) + BitVec.ofNat 64 (8 * i.val)) 8) i
    apply apart.ne (initial.regValue .rsp) hk hj (by cases keccak <;> cases fullState <;> cases mode <;> cases v <;> decide)
    rw [frameBase_sub_eight (keccak := keccak) (fullState := fullState)] at he
    simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc] using he.symm
  refine ⟨fun i ↦ (keep ⟨i.val, by omega⟩).trans (saved.saved i), ?_⟩
  have h := keep ⟨mode.pushCount fullState, by omega⟩
  simp only [BitVec.sub_add_cancel] at h
  exact h.trans saved.returnSlot

private theorem stateRegion_subset {initial : RamState} {v : Variant} {mode : Mode} {keccak fullState : Bool}
    (hStack : Stack.Valid initial (mode.entry v keccak fullState).minStackBytes)
    (hbudget : (mode.frameSize v keccak fullState) - (mode.stateOffset v keccak fullState) ≤ (mode.entry v keccak fullState).minStackBytes) :
    ∀ address : BitVec 64,
      (MemoryRegion.mk (statePointer initial v mode keccak fullState).toNat 201).Contains address.toNat →
      (Stack.region initial (mode.entry v keccak fullState).minStackBytes).Contains address.toNat := by
  rw [statePointer_sub (keccak := keccak) (fullState := fullState)]
  have hsub := stack_sub_toNat hStack.2.2.1 hbudget
  have hu := hStack.2.2.1
  change (mode.entry v keccak fullState).minStackBytes ≤ (initial.regValue .rsp).toNat at hu
  intro address hcontains
  change
    (initial.regValue .rsp - BitVec.ofNat 64 ((mode.frameSize v keccak fullState) - (mode.stateOffset v keccak fullState))).toNat ≤
        address.toNat ∧
      address.toNat <
        (initial.regValue .rsp - BitVec.ofNat 64 ((mode.frameSize v keccak fullState) - (mode.stateOffset v keccak fullState))).toNat + 201
    at hcontains
  rw [hsub] at hcontains
  simp only [Stack.region, Stack.returnAddressBytes, MemoryRegion.Contains]
  have hsize : 201 ≤ (mode.frameSize v keccak fullState) - (mode.stateOffset v keccak fullState) := by cases keccak <;> cases fullState <;> cases mode <;> cases v <;> decide
  omega

theorem initial_memset_pre [bindings : Bindings] {initial s : RamState}
    {v : Variant} {mode : Mode} {keccak fullState : Bool}
    {inputs : Array Input} {split : Nat} (boundary : ReturnBoundary) (ret : BitVec 64)
    (hCall : ValidInvocation bindings v mode initial inputs split keccak fullState)
    (hbudget : (mode.frameSize v keccak fullState) + 8 ≤ (mode.entry v keccak fullState).minStackBytes)
    (inv : Invariant initial v mode s keccak fullState)
    (ip : s.RIP = 0x106a20) (sp : stackPtr s = frameBase initial v mode keccak fullState - (8 : BitVec 64))
    (hr : stackTop s = ret) (retLow : ret.toNat < 2 ^ 32)
    (destination : (Operand.reg 7 : Operand 64).read s = statePointer initial v mode keccak fullState)
    (length : (Operand.reg 2 : Operand 64).read s = 201)
    (value : (Operand.reg 6 : Operand 64).read s = 0)
    (inside : frameBase initial v mode keccak fullState - (8 : BitVec 64) ≠ boundary.rsp)
    (afterReturn : frameBase initial v mode keccak fullState ≠ boundary.rsp) : Memset.Pre boundary s := by
  have hsize : 201 ≤ (mode.frameSize v keccak fullState) - (mode.stateOffset v keccak fullState) := by cases keccak <;> cases fullState <;> cases mode <;> cases v <;> decide
  have hp := statePointer_sub initial v mode keccak fullState
  have hptr : (statePointer initial v mode keccak fullState).toNat =
      (initial.regValue .rsp).toNat - ((mode.frameSize v keccak fullState) - (mode.stateOffset v keccak fullState)) := by
    rw [hp]
    exact stack_sub_toNat (offset := (mode.frameSize v keccak fullState) - (mode.stateOffset v keccak fullState))
      hCall.stackAvailable.2.2.1 (by omega)
  have hsp : (stackPtr s).toNat = (initial.regValue .rsp).toNat - ((mode.frameSize v keccak fullState) + 8) := by
    rw [sp, frameBase_sub_eight (keccak := keccak) (fullState := fullState)]
    exact stack_sub_toNat hCall.stackAvailable.2.2.1 hbudget
  have hu := hCall.stackAvailable.2.2.1
  change (mode.entry v keccak fullState).minStackBytes ≤ (initial.regValue .rsp).toNat at hu
  have hl := stack_sub_low hCall.stackAvailable hbudget
  have hreturn : stackPtr s + 8 = frameBase initial v mode keccak fullState := by rw [sp, BitVec.sub_add_cancel]
  refine ⟨ip, length, value, ?_, inv.direction, ?_, ?_, ?_, ?_, hr ▸ retLow,
    ?_, ?_, .inr (hreturn ▸ afterReturn)⟩
  · rw [destination, hptr]
    have halign := hCall.stackAvailable.2.2.2
    change (initial.regValue .rsp).toNat % 16 = 8 at halign
    cases keccak <;> cases fullState <;> cases mode <;> cases v <;> simp only [Mode.frameSize, Mode.stateOffset, Bool.false_eq_true, ↓reduceIte] at * <;> omega
  · rw [destination, hp]
    exact stackReadable inv hCall.stackAvailable
      (by omega : (mode.frameSize v keccak fullState) - (mode.stateOffset v keccak fullState) ≤ (mode.entry v keccak fullState).minStackBytes)
      (by cases keccak <;> cases fullState <;> cases mode <;> cases v <;> decide : 201 ≤ (mode.frameSize v keccak fullState) - (mode.stateOffset v keccak fullState))
  · rw [destination]
    intro address ha ht
    exact writeRegions_avoid hCall (Stack.region initial (mode.entry v keccak fullState).minStackBytes)
      (stack_mem_writeRegions initial v mode keccak fullState) address
      (stateRegion_subset hCall.stackAvailable (by omega) address ha) (.inr ht)
  · rw [destination]
    intro address ha ht
    exact writeRegions_avoid hCall (Stack.region initial (mode.entry v keccak fullState).minStackBytes)
      (stack_mem_writeRegions initial v mode keccak fullState) address
      (stateRegion_subset hCall.stackAvailable (by omega) address ha) (.inl ht)
  · rw [sp, frameBase_sub_eight (keccak := keccak) (fullState := fullState)]
    exact stackReadable inv hCall.stackAvailable hbudget (by omega)
  · rw [destination]
    apply RangeApart.of_toNat
    · rw [hptr]
      have hlow := stack_sub_low hCall.stackAvailable
        (by omega : (mode.frameSize v keccak fullState) - (mode.stateOffset v keccak fullState) ≤ (mode.entry v keccak fullState).minStackBytes)
      change
        (initial.regValue .rsp - BitVec.ofNat 64 ((mode.frameSize v keccak fullState) - (mode.stateOffset v keccak fullState))).toNat +
          ((mode.frameSize v keccak fullState) - (mode.stateOffset v keccak fullState)) < 2^32 at hlow
      rw [stack_sub_toNat hCall.stackAvailable.2.2.1 (by omega)] at hlow
      omega
    · rw [hsp]
      change (initial.regValue .rsp - BitVec.ofNat 64 ((mode.frameSize v keccak fullState) + 8)).toNat +
        ((mode.frameSize v keccak fullState) + 8) < 2^32 at hl
      rw [stack_sub_toNat hCall.stackAvailable.2.2.1 hbudget] at hl
      omega
    · rw [hptr, hsp]
      exact .inr (by omega)
  · exact sp ▸ inside

def initializationChanges (initial : RamState) (v : Variant) (mode : Mode) (keccak : Bool := false) (fullState : Bool := false) : List Component :=
  [.reg 4, .mem (frameBase initial v mode keccak fullState - (8 : BitVec 64)) 8, .rip] ++
    Memset.clobbers (statePointer initial v mode keccak fullState)

private theorem initialization_localFrame (initial : RamState) (v : Variant) (mode : Mode) (keccak : Bool := false) (fullState : Bool := false) :
    ∀ c ∈ initializationChanges initial v mode keccak fullState, ∀ address, c.Covers address →
      (Component.mem (frameBase initial v mode keccak fullState - (8 : BitVec 64))
        ((mode.frameSize v keccak fullState) - (8 * mode.pushCount fullState - 8))).Covers address := by
  intro c hc address hcover
  simp only [initializationChanges, List.mem_append, Memset.clobbers, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with (rfl | rfl | rfl) |
      (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals try exact hcover.elim
  · obtain ⟨i, hi, rfl⟩ := hcover
    exact ⟨i, by cases keccak <;> cases fullState <;> cases mode <;> cases v <;> simp only [Mode.frameSize, Mode.pushCount, Bool.false_eq_true, ↓reduceIte] <;> omega, rfl⟩
  · obtain ⟨i, hi, rfl⟩ := hcover
    refine ⟨8 + (mode.stateOffset v keccak fullState) + i, ?_, ?_⟩
    · cases keccak <;> cases fullState <;> cases mode <;> cases v <;> simp only [Mode.frameSize, Mode.stateOffset, Mode.pushCount, Bool.false_eq_true, ↓reduceIte] <;> omega
    · simp only [statePointer, BitVec.ofNat_add, ← BitVec.add_assoc]
      simp only [BitVec.ofNat_eq_ofNat, BitVec.sub_add_cancel]

theorem initialization_outputSlot {initial s t : RamState} {v : Variant} {mode : Mode} {keccak fullState : Bool}
    (ha : AgreesExcept (initializationChanges initial v mode keccak fullState) s t) :
    (Operand.mem (outputSlot initial v mode keccak fullState) : Operand 64).read t =
      (Operand.mem (outputSlot initial v mode keccak fullState) : Operand 64).read s := by
  apply readMem_agrees ha
  intro j hj c hc hcover
  simp only [initializationChanges, List.mem_append, Memset.clobbers, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with (rfl | rfl | rfl) |
      (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals try exact hcover.elim
  · obtain ⟨i, hi, he⟩ := hcover
    have apart : OffsetsApart (-(8 : BitVec 64)) 8
        (BitVec.ofNat 64 (mode.outputSlotOffset v keccak fullState)) 8 := by
      cases keccak <;> cases fullState <;> cases mode <;> cases v <;> unfold Mode.outputSlotOffset OffsetsApart <;> decide +kernel
    apply apart.ne (frameBase initial v mode keccak fullState) hi hj (by decide)
    simpa only [outputSlot, BitVec.sub_eq_add_neg] using he.symm
  · obtain ⟨i, hi, he⟩ := hcover
    have apart : OffsetsApart (BitVec.ofNat 64 (mode.stateOffset v keccak fullState)) 201
        (BitVec.ofNat 64 (mode.outputSlotOffset v keccak fullState)) 8 := by
      cases keccak <;> cases fullState <;> cases mode <;> cases v <;> unfold Mode.outputSlotOffset Mode.stateOffset OffsetsApart <;>
        decide +kernel
    apply apart.ne (frameBase initial v mode keccak fullState) hi hj (by decide)
    exact he.symm

structure Initialized (initial : RamState) (v : Variant) (mode : Mode) (s : RamState)
    (keccak : Bool := false) (fullState : Bool := false) : Prop where
  stack : stackPtr s = frameBase initial v mode keccak fullState
  saved : SavedFrame initial s mode fullState
  zero : ∀ i, i < 201 → s.external[statePointer initial v mode keccak fullState + BitVec.ofNat 64 i]? = some 0

private theorem initial_memset_steps_form [bindings : Bindings] (hstride : UnitStringStride bindings)
    {initial s : RamState} {v : Variant} {mode : Mode} {keccak fullState : Bool} {inputs : Array Input} {split : Nat}
    (boundary : ReturnBoundary) (p : BitVec 64) (disp : BitVec 32) (regCall : Bool)
    (hCall : ValidInvocation bindings v mode initial inputs split keccak fullState)
    (hbudget : (mode.frameSize v keccak fullState) + 8 ≤ (mode.entry v keccak fullState).minStackBytes)
    (image : ImageAt p (if regCall then [0x41, 0xff, 0xd5] else encodeCallM64 (.rip disp)))
    (target : if regCall then (Operand.reg 13 : Operand 64).read s = 0x106a20
      else (p + (6 : BitVec 64)) + disp.signExtend 64 = 0x200188)
    (retLow : (p + (if regCall then 3 else 6 : BitVec 64)).toNat < 2 ^ 32)
    (inv : Invariant initial v mode s keccak fullState) (saved : SavedFrame initial s mode fullState) (ip : s.RIP = p)
    (registers : SetupRegisters initial v mode s keccak fullState)
    (inside : frameBase initial v mode keccak fullState - (8 : BitVec 64) ≠ boundary.rsp)
    (afterReturn : frameBase initial v mode keccak fullState ≠ boundary.rsp) :
    ∃ t, Advances boundary 46 s t ∧ Invariant initial v mode t keccak fullState ∧
      t.RIP = p + (if regCall then 3 else 6 : BitVec 64) ∧ Initialized initial v mode t keccak fullState ∧
      AgreesExcept (initializationChanges initial v mode keccak fullState) s t ∧
      (Operand.mem (outputSlot initial v mode keccak fullState) : Operand 64).read t =
        (Operand.mem (outputSlot initial v mode keccak fullState) : Operand 64).read s := by
  have hsize : 201 ≤ (mode.frameSize v keccak fullState) - (mode.stateOffset v keccak fullState) := by cases keccak <;> cases fullState <;> cases mode <;> cases v <;> decide
  obtain ⟨u, hsu, iu, ipu, spu, retu, au⟩ :=
    initial_memset_call_form boundary p disp regCall hCall hbudget image target inv ip registers.stack inside
  have hreg (r : BitVec 5) (hr : r ≠ 4) :
      (Operand.reg r : Operand 64).read u = (Operand.reg r : Operand 64).read s :=
    au.read (by simp only [List.mem_cons, List.not_mem_nil, or_false,
      Component.reg.injEq, reduceCtorEq, or_false]; exact hr)
  have hdst : (Operand.reg 7 : Operand 64).read u = statePointer initial v mode keccak fullState :=
    (hreg 7 (by decide)).trans registers.destination
  have hpre := initial_memset_pre boundary (p + (if regCall then 3 else 6)) hCall hbudget iu ipu spu retu retLow
    hdst ((hreg 2 (by decide)).trans registers.length)
    ((hreg 6 (by decide)).trans registers.value) inside afterReturn
  obtain ⟨t, hut, done⟩ := Memset.memset201_steps hstride boundary u iu.ready iu.code hpre
  have aft : AgreesExcept (Memset.clobbers (statePointer initial v mode keccak fullState)) u t :=
    hdst ▸ done.agrees
  have frame : AgreesExcept (initializationChanges initial v mode keccak fullState) s t := au.trans aft
  have it : Invariant initial v mode t keccak fullState := iu.of_agreesExcept hCall done.ready aft (by
    apply Memset.clobbers_writesWithin
    intro i hi
    refine ⟨Stack.region initial (mode.entry v keccak fullState).minStackBytes,
      stack_mem_writeRegions initial v mode keccak fullState, ?_⟩
    rw [statePointer_sub (keccak := keccak) (fullState := fullState)]
    exact stack_sub_contains (offset := (mode.frameSize v keccak fullState) - (mode.stateOffset v keccak fullState))
      hCall.stackAvailable (by omega) (by omega)) (by simp [Memset.clobbers])
  refine ⟨t, hsu.trans hut, it, done.rip.trans retu,
    ⟨?_, saved.of_localFrame frame (initialization_localFrame initial v mode keccak fullState), ?_⟩,
    frame, initialization_outputSlot frame⟩
  · rw [done.rsp, spu, BitVec.sub_add_cancel]
  · simpa only [hdst] using done.zero

theorem initial_memset_steps [bindings : Bindings] (hstride : UnitStringStride bindings)
    {initial s : RamState} {v : Variant} {mode : Mode} {keccak fullState : Bool} {inputs : Array Input} {split : Nat}
    (boundary : ReturnBoundary) (p : BitVec 64) (disp : BitVec 32)
    (hCall : ValidInvocation bindings v mode initial inputs split keccak fullState)
    (hbudget : (mode.frameSize v keccak fullState) + 8 ≤ (mode.entry v keccak fullState).minStackBytes)
    (image : ImageAt p (encodeCallM64 (.rip disp)))
    (target : (p + (6 : BitVec 64)) + disp.signExtend 64 = 0x200188)
    (retLow : (p + (6 : BitVec 64)).toNat < 2 ^ 32)
    (inv : Invariant initial v mode s keccak fullState) (saved : SavedFrame initial s mode fullState) (ip : s.RIP = p)
    (registers : SetupRegisters initial v mode s keccak fullState)
    (inside : frameBase initial v mode keccak fullState - (8 : BitVec 64) ≠ boundary.rsp)
    (afterReturn : frameBase initial v mode keccak fullState ≠ boundary.rsp) :
    ∃ t, Advances boundary 46 s t ∧ Invariant initial v mode t keccak fullState ∧
      t.RIP = p + (6 : BitVec 64) ∧ Initialized initial v mode t keccak fullState ∧
      AgreesExcept (initializationChanges initial v mode keccak fullState) s t ∧
      (Operand.mem (outputSlot initial v mode keccak fullState) : Operand 64).read t =
        (Operand.mem (outputSlot initial v mode keccak fullState) : Operand 64).read s := by
  exact initial_memset_steps_form hstride boundary p disp false hCall hbudget image target retLow
    inv saved ip registers inside afterReturn

theorem initial_memset_register_steps [bindings : Bindings] (hstride : UnitStringStride bindings)
    {initial s : RamState} {v : Variant} {mode : Mode} {keccak fullState : Bool} {inputs : Array Input} {split : Nat}
    (boundary : ReturnBoundary) (p : BitVec 64)
    (hCall : ValidInvocation bindings v mode initial inputs split keccak fullState)
    (hbudget : (mode.frameSize v keccak fullState) + 8 ≤ (mode.entry v keccak fullState).minStackBytes)
    (image : ImageAt p [0x41, 0xff, 0xd5])
    (target : (Operand.reg 13 : Operand 64).read s = 0x106a20)
    (retLow : (p + (3 : BitVec 64)).toNat < 2 ^ 32)
    (inv : Invariant initial v mode s keccak fullState) (saved : SavedFrame initial s mode fullState) (ip : s.RIP = p)
    (registers : SetupRegisters initial v mode s keccak fullState)
    (inside : frameBase initial v mode keccak fullState - (8 : BitVec 64) ≠ boundary.rsp)
    (afterReturn : frameBase initial v mode keccak fullState ≠ boundary.rsp) :
    ∃ t, Advances boundary 46 s t ∧ Invariant initial v mode t keccak fullState ∧
      t.RIP = p + (3 : BitVec 64) ∧ Initialized initial v mode t keccak fullState ∧
      AgreesExcept (initializationChanges initial v mode keccak fullState) s t ∧
      (Operand.mem (outputSlot initial v mode keccak fullState) : Operand 64).read t =
        (Operand.mem (outputSlot initial v mode keccak fullState) : Operand 64).read s := by
  exact initial_memset_steps_form hstride boundary p 0 true hCall hbudget image target retLow
    inv saved ip registers inside afterReturn

end Sha3.Proofs.Wrapper
