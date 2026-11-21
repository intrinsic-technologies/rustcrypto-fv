import Sha3.Proofs.Wrapper.Loop.Memory

namespace Sha3.Proofs.Wrapper.Loop

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

variable {keccak fullState : Bool}

theorem component_covers_of_contains {pointer address : BitVec 64} {count : Nat}
    (h : (⟨pointer.toNat, count⟩ : MemoryRegion).Contains address.toNat) :
    (Component.mem pointer count).Covers address := by
  refine ⟨address.toNat - pointer.toNat, by change pointer.toNat ≤ address.toNat ∧
      address.toNat < pointer.toNat + count at h; omega, ?_⟩
  apply BitVec.eq_of_toNat_eq
  have hmax := address.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  have hmin : pointer.toNat ≤ address.toNat := h.1
  omega

theorem frame_agrees_memory {initial s t : RamState} {v : Variant} {kind : Kind}
    (h : MemoryWriteFrame s t (writeRegions (keccak := keccak) (fullState := fullState) initial v kind)) :
    ∀ address, (∀ c ∈ clobbers (keccak := keccak) (fullState := fullState) initial v kind, ¬ c.Covers address) →
      t.external[address]? = s.external[address]? := by
  intro address ha
  apply h address
  intro region hr hcontains
  simp only [writeRegions, Vector.mem_mk, List.mem_toArray, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ha _ (by simp [clobbers]) (component_covers_of_contains hcontains)
  · exact ha _ (by simp [clobbers]) (component_covers_of_contains hcontains)

theorem reg_not_clobbered {initial : RamState} {kind : Kind} {r : BitVec 5}
    (h : Component.reg r ∉ clobbers (keccak := keccak) (fullState := fullState) initial v kind) :
    r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 12 ∨ r = 13 ∨ r = 14 ∨ r = 15 := by
  have hlo : r.toNat < 16 := by
    by_cases hlo : r.toNat < 16
    · exact hlo
    · apply False.elim
      apply h
      apply List.mem_append_right
      apply List.mem_append_left
      apply List.mem_ofFn.mpr
      refine ⟨⟨r.toNat - 16, by have := r.isLt; omega⟩, ?_⟩
      simp only [Nat.add_sub_cancel' (by omega : 16 ≤ r.toNat), BitVec.ofNat_toNat,
        BitVec.setWidth_eq]
  simp only [clobbers, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    not_or, Component.reg.injEq] at h
  simp only [BitVec.toNat_eq, BitVec.reduceToNat] at h ⊢
  omega

theorem xmm_mem_clobbers (initial : RamState) (v : Variant) (kind : Kind) (r : BitVec 5) :
    Component.xmm r ∈ clobbers (keccak := keccak) (fullState := fullState) initial v kind := by
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_ofFn.mpr
  exact ⟨⟨r.toNat, r.isLt⟩, by simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩

theorem after_update {initial s called final : RamState} {v : Variant} {kind : Kind}
    {stop : Nat} {state : Incremental.State}
    (hStack : Stack.Valid initial (kind.mode.entry v (keccak := keccak) (fullState := fullState)).minStackBytes)
    (hRegs : Registers (keccak := keccak) (fullState := fullState) initial v kind stop s)
    (hsp : called.regValue .rsp = frameBase (keccak := keccak) (fullState := fullState) initial v kind.mode - 8)
    (hp : called.regValue .rsi = statePointer (keccak := keccak) (fullState := fullState) initial v kind.mode)
    (ha : AgreesExcept [.reg 4, .mem (frameBase (keccak := keccak) (fullState := fullState) initial v kind.mode - 8) 8, .rip] s called)
    (hresult : Update.CallResult called final state) :
    AgreesExcept (clobbers (keccak := keccak) (fullState := fullState) initial v kind) s final ∧ Registers (keccak := keccak) (fullState := fullState) initial v kind stop final ∧
      (Operand.reg (kind.nextReg v fullState) : Operand 64).read final =
        (Operand.reg (kind.nextReg v fullState) : Operand 64).read s := by
  have hcallSaved : CalleeSavedRegistersUnchanged s called :=
    calleeSavedRegistersUnchanged_of_agreesExcept ha (by
      intro register hregister
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hregister
      rcases hregister with rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> decide +kernel)
  have hsaved : CalleeSavedRegistersUnchanged s final :=
    fun register hr ↦ (hresult.saved register hr).trans (hcallSaved register hr)
  have hkeep (r : BitVec 5) (hr : r ∈ [3, 5, 12, 13, 14, 15]) :
      (Operand.reg r : Operand 64).read final = (Operand.reg r : Operand 64).read s := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsaved .rbx (by simp)
    · exact hsaved .rbp (by simp)
    · exact hsaved .r12 (by simp)
    · exact hsaved .r13 (by simp)
    · exact hsaved .r14 (by simp)
    · exact hsaved .r15 (by simp)
  have hfinalsp : final.regValue .rsp = frameBase (keccak := keccak) (fullState := fullState) initial v kind.mode := by
    rw [hresult.stack, hsp, BitVec.sub_add_cancel]
  have hslot : frameBase (keccak := keccak) (fullState := fullState) initial v kind.mode - 8 = stackBase (keccak := keccak) (fullState := fullState) initial v kind + 328 := by
    simp only [stackBase, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have hcallWrites : WritesWithin
      [.reg 4, .mem (frameBase (keccak := keccak) (fullState := fullState) initial v kind.mode - 8) 8, .rip]
      (writeRegions (keccak := keccak) (fullState := fullState) initial v kind) := by
    intro c hc address hcover
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact hcover.elim
    · obtain ⟨j, hj, he⟩ := hcover
      apply clobbers_writesWithin hStack (.mem (stackBase (keccak := keccak) (fullState := fullState) initial v kind) 336)
        (by simp [clobbers]) address
      refine ⟨328 + j, by omega, ?_⟩
      rw [he, hslot, BitVec.add_assoc, BitVec.ofNat_add]
      rfl
    · exact hcover.elim
  have hmemory : MemoryWriteFrame s final (writeRegions (keccak := keccak) (fullState := fullState) initial v kind) :=
    memoryWriteFrame_trans (ha.memoryWriteFrame hcallWrites)
      (memoryWriteFrame_mono hresult.memory (update_writeRegions_subset hsp hp))
  have hagrees : AgreesExcept (clobbers initial v kind keccak fullState) s final := by
    have hframe := hresult.rest.trans (ha.scalarFrame_eq (by rfl))
    refine ⟨?_, frame_agrees_memory hmemory, congrArg ScalarFrame.rest hframe,
      fun address hmem ↦ hresult.grows address (ha.grow address hmem)⟩
    intro c hc hm
    cases c with
    | reg r =>
      rcases reg_not_clobbered hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hkeep 3 (by simp)
      · exact hfinalsp.trans hRegs.stack.symm
      · exact hkeep 5 (by simp)
      · exact hkeep 12 (by simp)
      · exact hkeep 13 (by simp)
      · exact hkeep 14 (by simp)
      · exact hkeep 15 (by simp)
    | flags => exact (hc (by simp [clobbers])).elim
    | rip => exact (hc (by simp [clobbers])).elim
    | mem address count => cases hm
    | xmm r => exact (hc (xmm_mem_clobbers initial v kind r)).elim
    | df => exact congrArg ScalarFrame.direction hframe
    | mxcsr => exact congrArg ScalarFrame.mxcsr hframe
    | fpr r => exact congrArg (fun frame => frame.fpr r) hframe
    | fsw => exact congrArg ScalarFrame.fsw hframe
    | fcc => exact congrArg ScalarFrame.fcc hframe
    | ftw => exact congrArg ScalarFrame.ftw hframe
    | fcw => exact congrArg ScalarFrame.fcw hframe
    | fpuPtr => exact congrArg ScalarFrame.fpuPtr hframe
  refine ⟨hagrees, ?_, ?_⟩
  · refine ⟨hfinalsp, (hsaved .r12 (by simp)).trans hRegs.pointers,
      (hsaved .r14 (by simp)).trans hRegs.lengths, ?_, ?_, ?_⟩
    · have hbound := hRegs.bound
      by_cases hm : kind.memoryBound v fullState = true
      · have hslot : (if fullState then 8 else 0) + 8 ≤ kind.mode.stateOffset v keccak fullState := by
          cases keccak <;> cases fullState <;> cases kind <;> cases v <;>
            simp [Kind.memoryBound, Kind.largeFollower] at hm <;> decide +kernel
        have he := preserves_slot hagrees hslot
        simp only [Kind.boundOperand, hm, ↓reduceIte] at hbound ⊢
        change (Operand.mem (s.regValue .rsp + _) : Operand 64).read s = _ at hbound
        change (Operand.mem (final.regValue .rsp + _) : Operand 64).read final = _
        rw [hRegs.stack] at hbound
        rw [hfinalsp]
        cases fullState <;> exact he.trans hbound
      · simp only [Kind.boundOperand, hm] at hbound ⊢
        exact (hkeep (kind.boundReg v fullState) (by
          cases fullState <;> cases kind <;> cases v <;>
            simp [Kind.boundReg, Kind.largeFollower])).trans hbound
    · exact (hkeep (kind.stateReg v fullState) (by cases fullState <;> cases kind <;> cases v <;> simp [Kind.stateReg, Kind.largeFollower])).trans hRegs.pointer
    · intro r hr
      exact (hkeep r (by
        cases fullState <;> cases kind <;> cases v <;>
          simp [Kind.cursorReg, Kind.largeFollower] at hr <;> subst r <;> simp)).trans (hRegs.cursor r hr)
  · exact hkeep (kind.nextReg v fullState) (by cases fullState <;> cases kind <;> cases v <;> simp [Kind.nextReg, Kind.largeFollower])

end Sha3.Proofs.Wrapper.Loop
