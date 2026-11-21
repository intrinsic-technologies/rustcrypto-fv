import Sha3.Proofs.Wrapper.Finish.Copy.Layout
import Sha3.Proofs.Wrapper.Finish.Call
import Sha3.Proofs.Wrapper.Setup.Initialize
import Sha3.Proofs.Memcpy
import Sha3.Proofs.Incremental.State
import Sha3.Proofs.Permutation.Layout

namespace Sha3.Proofs.Wrapper.Finish.Copy

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

def changes (initial : RamState) (v : Variant := .sha224)
    (mode : Mode := .finalizeReset) (destination : Nat := 232)
    (keccak : Bool := false) (fullState : Bool := false) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 4, .reg 6, .reg 7, .reg 8, .reg 3, .flags, .rip,
    .mem (frameBase initial v mode keccak fullState - 8) 8,
    .mem (frameBase initial v mode keccak fullState + BitVec.ofNat 64 destination) 208]

theorem changes_trans {initial s t u : RamState}
    {v : Variant} {mode : Mode} {destination : Nat} {keccak fullState : Bool}
    (h : AgreesExcept (changes initial v mode destination keccak fullState) s t)
    (h' : AgreesExcept (changes initial v mode destination keccak fullState) t u) :
    AgreesExcept (changes initial v mode destination keccak fullState) s u :=
  (h.trans h').mono fun _ hc ↦ (List.mem_append.mp hc).elim id id

theorem changes_local (initial : RamState) (v : Variant) (mode : Mode)
    (destination : Nat) (keccak fullState : Bool) (hFits : destination + 208 + (8 * mode.pushCount fullState) ≤ mode.frameSize v keccak fullState) :
    ∀ c ∈ changes initial v mode destination keccak fullState, ∀ address, c.Covers address →
      (Component.mem (frameBase initial v mode keccak fullState - 8) (mode.frameSize v keccak fullState - (8 * mode.pushCount fullState - 8))).Covers address := by
  have hCount : 8 ≤ 8 * mode.pushCount fullState := by
    cases mode <;> cases fullState <;> decide
  intro c hc address hcover
  simp only [changes, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    try exact hcover.elim
  · obtain ⟨i, hi, he⟩ := hcover
    exact ⟨i, by omega, he⟩
  · obtain ⟨i, hi, rfl⟩ := hcover
    refine ⟨(8 + destination) + i, by omega, ?_⟩
    rw [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, ← BitVec.add_assoc]
    congr 1
    change frameBase initial v mode keccak fullState + BitVec.ofNat 64 destination =
      frameBase initial v mode keccak fullState - 8 + BitVec.ofNat 64 (8 + destination)
    rw [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat,
      ← BitVec.add_assoc, BitVec.sub_add_cancel]

theorem changes_saved {initial s t : RamState}
    {v : Variant} {mode : Mode} {destination : Nat} {keccak fullState : Bool} (saved : SavedFrame initial s mode fullState)
    (h : AgreesExcept (changes initial v mode destination keccak fullState) s t)
    (hFits : destination + 208 + (8 * mode.pushCount fullState) ≤ mode.frameSize v keccak fullState) : SavedFrame initial t mode fullState :=
  saved.of_localFrame (v := v) (mode := mode) h
    (changes_local initial v mode destination keccak fullState hFits)

theorem changes_writes {initial : RamState} {v : Variant} {mode : Mode}
    {destination : Nat} {keccak fullState : Bool}
    (hStack : Stack.Valid initial (mode.entry v keccak fullState).minStackBytes)
    (hFits : destination + 208 + (8 * mode.pushCount fullState) ≤ mode.frameSize v keccak fullState) :
    WritesWithin (changes initial v mode destination keccak fullState)
      #v[Stack.region initial (mode.entry v keccak fullState).minStackBytes] := by
  intro c hc address hcover
  obtain ⟨i, hi, rfl⟩ := changes_local initial v mode destination keccak fullState hFits c hc address hcover
  refine ⟨_, Vector.mem_iff_getElem.mpr ⟨0, by decide, rfl⟩, ?_⟩
  rw [frameBase_sub_eight initial v mode keccak fullState]
  exact stack_sub_contains hStack (by rw [Mode.stackBudget mode v keccak fullState]; omega) (by omega)

theorem destination_writes {initial : RamState} {v : Variant} {mode : Mode}
    {destination : Nat} {keccak fullState : Bool}
    (hStack : Stack.Valid initial (mode.entry v keccak fullState).minStackBytes)
    (hFits : destination + 208 ≤ mode.frameSize v keccak fullState + 8) :
    WritesWithin (Memcpy.clobbers (frameBase initial v mode keccak fullState + BitVec.ofNat 64 destination))
      (writeRegions initial v mode keccak fullState) := by
  apply Memcpy.clobbers_writesWithin
  intro i hi
  refine ⟨_, stack_mem_writeRegions initial v mode keccak fullState, ?_⟩
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact frameAddress_contains hStack (by rw [Mode.stackBudget mode v keccak fullState]; omega) (by omega)

abbrev memcpyPointer_bytes := @Memcpy.memcpyPointer_bytes
abbrev memcpyPointer_read := @Memcpy.memcpyPointer_read
abbrev memcpyPointer_readable := @Memcpy.memcpyPointer_readable

theorem callImage (v : Variant) (mode : Mode := .finalizeReset) (keccak : Bool := false)
    (fullState : Bool := false) (hMode : mode.hasBeforeOutput = true := by decide) :
    ∀ x ∈ codeRange (callPC v mode keccak fullState) (encodeCallM64 (.rip (callDisp v mode keccak fullState))),
      x ∈ Extracted.programImage := by
  have h : ImageAt (callPC v mode keccak fullState) (encodeCallM64 (.rip (callDisp v mode keccak fullState))) := by
    unfold ImageAt
    cases mode <;> cases v <;> cases keccak <;> cases fullState <;>
      first | contradiction | decide +kernel
  intro x hx
  exact imageSections_mem_toCodeMap_of_fetchByte (h x hx).2

theorem callTarget (v : Variant) (mode : Mode := .finalizeReset) (keccak : Bool := false)
    (fullState : Bool := false) (hMode : mode.hasBeforeOutput = true := by decide) :
    (callPC v mode keccak fullState + 6) + (callDisp v mode keccak fullState).signExtend 64 = 0x200180 := by
  cases mode <;> cases v <;> cases keccak <;> cases fullState <;>
      first | contradiction | decide +kernel

theorem call_steps [bindings : Bindings] {initial s : RamState} {v : Variant} {mode : Mode} {keccak fullState : Bool}
    {inputs : Array Input} {split : Nat}
    (hCall : ValidInvocation bindings v mode initial inputs split keccak fullState)
    (hMode : mode.hasBeforeOutput = true)
    (inv : Invariant initial v mode s keccak fullState) (ip : s.RIP = callPC v mode keccak fullState)
    (sp : stackPtr s = frameBase initial v mode keccak fullState) :
    ∃ t, Advances (returnBoundary initial) 1 s t ∧ Invariant initial v mode t keccak fullState ∧
      t.RIP = (0x106a70 : BitVec 64) ∧
      stackPtr t = frameBase initial v mode keccak fullState - 8 ∧ stackTop t = callPC v mode keccak fullState + 6 ∧
      AgreesExcept [.reg 4, .mem (frameBase initial v mode keccak fullState - 8) 8, .rip] s t := by
  have target : callMemPtr (callPC v mode keccak fullState) (.rip (callDisp v mode keccak fullState)) s = 0x106a70 := by
    change (Operand.mem ((callPC v mode keccak fullState + 6) + (callDisp v mode keccak fullState).signExtend 64) : Operand 64).read s = _
    rw [callTarget v mode keccak fullState hMode]
    exact memcpyPointer_read inv.loaded
  obtain ⟨t, ha, ht, hrip, hrsp, htop, hagree, _⟩ :=
    indirectCallAt (mode.frameSize v keccak fullState) (callPC v mode keccak fullState) (callDisp v mode keccak fullState) hCall
      (by rw [Mode.stackBudget mode v keccak fullState]; omega) (layout_bounds mode v keccak fullState hMode).2.2.2.2.1 inv ip sp (callImage v mode keccak fullState hMode)
      (by change MemReadable s ((callPC v mode keccak fullState + 6) + (callDisp v mode keccak fullState).signExtend 64) 8
          rw [callTarget v mode keccak fullState hMode]; exact memcpyPointer_readable inv.loaded)
      (by rw [target]; decide)
  have he : initial.regValue .rsp - BitVec.ofNat 64 (mode.frameSize v keccak fullState + 8) =
      frameBase initial v mode keccak fullState - 8 := (frameBase_sub_eight initial v mode keccak fullState).symm
  rw [he] at hrsp hagree
  exact ⟨t, ha, ht, hrip.trans target, hrsp, htop, hagree⟩

theorem memcpy_pre [bindings : Bindings] {initial s : RamState} {v : Variant} {mode : Mode} {keccak fullState : Bool}
    {inputs : Array Input} {split : Nat}
    (hCall : ValidInvocation bindings v mode initial inputs split keccak fullState)
    (hMode : mode.hasBeforeOutput = true)
    (inv : Invariant initial v mode s keccak fullState)
    (ip : s.RIP = (0x106a70 : BitVec 64))
    (sp : stackPtr s = frameBase initial v mode keccak fullState - 8)
    (dst : (Operand.reg 7 : Operand 64).read s = frameBase initial v mode keccak fullState + BitVec.ofNat 64 (destinationOffset mode v fullState))
    (src : (Operand.reg 6 : Operand 64).read s = frameBase initial v mode keccak fullState + BitVec.ofNat 64 (mode.stateOffset v keccak fullState))
    (len : (Operand.reg 2 : Operand 64).read s = 208)
    (ret : stackTop s = callPC v mode keccak fullState + 6) : Memcpy.Pre (returnBoundary initial) s := by
  obtain ⟨hd, hs, hApart, hdAlign, hfAlign, hfSmall, hPush⟩ := layout_bounds mode v keccak fullState hMode
  have hStack := hCall.stackAvailable
  have budget : (mode.frameSize v keccak fullState) ≤ (mode.entry v keccak fullState).minStackBytes := by
    rw [Mode.stackBudget mode v keccak fullState]; omega
  have destRead : MemReadable s (frameBase initial v mode keccak fullState + BitVec.ofNat 64 (destinationOffset mode v fullState)) 208 :=
    inv.frameReadable hStack (by omega)
  have sourceRead : MemReadable s (frameBase initial v mode keccak fullState + BitVec.ofNat 64 (mode.stateOffset v keccak fullState)) 208 :=
    inv.frameReadable hStack (by omega)
  have destNat : (frameBase initial v mode keccak fullState + BitVec.ofNat 64 (destinationOffset mode v fullState)).toNat =
      (frameBase initial v mode keccak fullState).toNat + destinationOffset mode v fullState :=
    frameAddress_toNat hStack budget (offset := destinationOffset mode v fullState) (by omega)
  have srcNat : (frameBase initial v mode keccak fullState + BitVec.ofNat 64 (mode.stateOffset v keccak fullState)).toNat =
      (frameBase initial v mode keccak fullState).toNat + mode.stateOffset v keccak fullState :=
    frameAddress_toNat hStack budget (offset := mode.stateOffset v keccak fullState) (by omega)
  have destCover : ∀ address,
      (MemoryRegion.mk (frameBase initial v mode keccak fullState + BitVec.ofNat 64 (destinationOffset mode v fullState)).toNat 208).Contains address →
      (Stack.region initial (mode.entry v keccak fullState).minStackBytes).Contains address := by
    intro address ha
    obtain ⟨hLo, hHi⟩ := frameBase_bounds (v := v) (mode := mode) (keccak := keccak) (fullState := fullState) hStack budget
    change (frameBase initial v mode keccak fullState + BitVec.ofNat 64 (destinationOffset mode v fullState)).toNat ≤ address ∧
      address < (frameBase initial v mode keccak fullState + BitVec.ofNat 64 (destinationOffset mode v fullState)).toNat + 208 at ha
    change _ ≤ address ∧ address < _
    rw [destNat] at ha
    omega
  have stackRead : MemReadable s (frameBase initial v mode keccak fullState - 8) 8 := by
    rw [frameBase_sub_eight initial v mode keccak fullState]
    have hb : (mode.frameSize v keccak fullState + 8) ≤ (mode.entry v keccak fullState).minStackBytes := by
      rw [Mode.stackBudget mode v keccak fullState]; omega
    refine ⟨?_, ?_⟩
    · have hl := stack_sub_low hStack hb
      change _ + (mode.frameSize v keccak fullState + 8) < 2^32 at hl
      change (initial.regValue .rsp - BitVec.ofNat 64 (mode.frameSize v keccak fullState + 8)).toNat + 8 ≤ 2^32
      omega
    · intro i hi
      exact inv.grows _ (Option.isSome_iff_exists.mpr
        (stack_sub_allocated hStack hb (by omega)))
  refine ⟨ip, len, ?_, inv.direction, src ▸ sourceRead, dst ▸ destRead, ?_, ?_, ?_,
    sp ▸ stackRead, ?_, ?_, ?_, ?_⟩
  · rw [dst, destNat]
    have hf : (frameBase initial v mode keccak fullState).toNat = (initial.regValue .rsp).toNat - mode.frameSize v keccak fullState :=
      stack_sub_toNat hStack.2.2.1 budget
    rw [hf]
    have ha := hStack.2.2.2
    change (initial.regValue .rsp).toNat % 16 = 8 at ha
    have hu : mode.frameSize v keccak fullState + 464 ≤ (initial.regValue .rsp).toNat := by
      have hu := hStack.2.2.1
      rw [Mode.stackBudget mode v keccak fullState] at hu
      exact hu
    change ((initial.regValue .rsp).toNat - mode.frameSize v keccak fullState + destinationOffset mode v fullState) % 8 = 0
    omega
  · rw [src, dst, srcNat, destNat]
    rcases hApart with hApart | hApart
    · exact .inl (by omega)
    · exact .inr (by omega)
  · rw [dst]
    intro address ha ht
    exact writeRegions_avoid hCall _ (stack_mem_writeRegions initial v mode keccak fullState)
      address (destCover _ ha) (.inr ht)
  · rw [dst]
    intro address ha hp
    exact writeRegions_avoid hCall _ (stack_mem_writeRegions initial v mode keccak fullState)
      address (destCover _ ha) (.inl hp)
  · rw [ret]
    cases mode <;> cases v <;> cases keccak <;> cases fullState <;>
      first | contradiction | decide +kernel
  · rw [dst, sp]
    have he : frameBase initial v mode keccak fullState + BitVec.ofNat 64 (destinationOffset mode v fullState) =
        (frameBase initial v mode keccak fullState - 8) +
          BitVec.ofNat 64 (8 + destinationOffset mode v fullState) := by
      rw [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, ← BitVec.add_assoc, BitVec.sub_add_cancel]
    rw [he]
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      RangeApart.offsets (frameBase initial v mode keccak fullState - 8)
        (a := 8 + destinationOffset mode v fullState) (b := 0) (len := 208) (count := 8)
        (by omega) (by decide) (.inr (by omega))
  · rw [sp, frameBase_sub_eight initial v mode keccak fullState]
    apply stackSub_ne_returnBoundary
    cases mode <;> cases v <;> cases keccak <;> cases fullState <;> decide +kernel
  · right
    rw [sp, BitVec.sub_add_cancel]
    apply stackSub_ne_returnBoundary
    cases mode <;> cases v <;> cases keccak <;> cases fullState <;> decide +kernel

theorem changes_byte {initial s t : RamState} {offset : Nat}
    {v : Variant} {mode : Mode} {destination : Nat} {keccak fullState : Bool}
    (h : AgreesExcept (changes initial v mode destination keccak fullState) s t)
    (ho : offset < destination ∨ destination + 208 ≤ offset)
    (hOffset : offset + 9 ≤ 2 ^ 64) (hDest : destination + 208 ≤ 2 ^ 64) :
    t.external[frameBase initial v mode keccak fullState + BitVec.ofNat 64 offset]? =
      s.external[frameBase initial v mode keccak fullState + BitVec.ofNat 64 offset]? := by
  apply h.byte
  intro c hc hcover
  simp only [changes, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    try exact hcover.elim
  · obtain ⟨i, hi, he⟩ := hcover
    have hb : frameBase initial v mode keccak fullState + BitVec.ofNat 64 offset =
        (frameBase initial v mode keccak fullState - 8) + BitVec.ofNat 64 (8 + offset) := by
      rw [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, ← BitVec.add_assoc,
        BitVec.sub_add_cancel]
    have apart := RangeApart.offsets (frameBase initial v mode keccak fullState - 8)
      (a := 0) (b := 8 + offset) (len := 8) (count := 1)
      (by decide) (by omega) (.inl (by omega))
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at apart
    exact apart i hi 0 (by decide) (by simpa using he.symm.trans hb)
  · obtain ⟨i, hi, he⟩ := hcover
    have apart := RangeApart.offsets (frameBase initial v mode keccak fullState)
      (a := destination) (b := offset) (len := 208) (count := 1)
      (by omega) (by omega) (by
        rcases ho with ho | ho
        · exact .inr (by omega)
        · exact .inl (by omega))
    exact apart i hi 0 (by decide) (by
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using he.symm)

theorem changes_read {initial s t : RamState} {offset width : Nat}
    {v : Variant} {mode : Mode} {destination : Nat} {keccak fullState : Bool}
    (h : AgreesExcept (changes initial v mode destination keccak fullState) s t)
    (ho : offset + width / 8 ≤ destination ∨ destination + 208 ≤ offset)
    (hOffset : offset + width / 8 + 8 ≤ 2 ^ 64)
    (hDest : destination + 208 ≤ 2 ^ 64) :
    (Operand.mem (frameBase initial v mode keccak fullState + BitVec.ofNat 64 offset) : Operand width).read t =
      (Operand.mem (frameBase initial v mode keccak fullState + BitVec.ofNat 64 offset) : Operand width).read s := by
  apply memLoad_congr
  intro i hi
  apply congrArg (fun x : Option UInt8 ↦ x.getD 0)
  change t.external[frameBase initial v mode keccak fullState + BitVec.ofNat 64 offset +
    BitVec.ofNat 64 i]? = s.external[_]?
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact changes_byte h (by rcases ho with ho | ho <;> omega) (by omega) hDest

theorem copied_read {s t : RamState} {src dst : BitVec 64} {offset width : Nat}
    (copy : ∀ i < 208, t.external[dst + BitVec.ofNat 64 i]? =
      s.external[src + BitVec.ofNat 64 i]?) (ho : offset + width / 8 ≤ 208) :
    (Operand.mem (dst + BitVec.ofNat 64 offset) : Operand width).read t =
      (Operand.mem (src + BitVec.ofNat 64 offset) : Operand width).read s := by
  apply memLoad_congr
  intro i hi
  apply congrArg (fun x : Option UInt8 ↦ x.getD 0)
  change t.external[dst + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? = s.external[_]?
  rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact copy _ (by omega)

end Sha3.Proofs.Wrapper.Finish.Copy
