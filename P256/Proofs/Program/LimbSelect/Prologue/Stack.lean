import P256.Proofs.Program.LimbSelect.Memory

set_option autoImplicit false

open P256.Proofs.Program (inProgram_of_textOffset memoryRegion_contains_add stack_region_end)

namespace P256.Proofs.Program.LimbSelect

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings] {s t u : RamState} {boundary : ReturnBoundary}

omit [Bindings] in
theorem stack_offset {t : RamState} {initial : BitVec 64} {offset : Nat}
    (hsp : t.regValue .rsp = initial - 72) (ho : offset ≤ 72) (next : BitVec 64) :
    (AddrMode.sib 4 none 0 (.d8 (BitVec.ofNat 8 offset))).addr t next =
      initial - BitVec.ofNat 64 (72-offset) := by
  have hsmall : (BitVec.ofNat 8 offset).toNat < 128 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  simp only [AddrMode.addr, Disp.value]
  change t.regValue .rsp + (BitVec.ofNat 8 offset).signExtend 64 = _
  rw [hsp]
  have he : (BitVec.ofNat 8 offset).signExtend 64 = BitVec.ofNat 64 offset := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_signExtend]
    have hn : (BitVec.ofNat 8 offset).msb = false := by
      apply BitVec.msb_eq_false_iff_two_mul_lt.mpr
      omega
    rw [hn]
    simp only [Bool.false_eq_true, ↓reduceIte, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  rw [he]
  have heq : (72 : BitVec 64) = BitVec.ofNat 64 (72-offset) + BitVec.ofNat 64 offset := by
    rw [← BitVec.ofNat_add, Nat.sub_add_cancel ho]
    rfl
  rw [heq, ← BitVec.sub_sub, BitVec.sub_add_cancel]

theorem stack_offset_code (hp : Pre s boundary) {offset len p lenCode : Nat}
    (ho : offset ≤ 80) (hl : len ≤ offset+8) (hc : p+lenCode ≤ 118431) :
    RangeApart (stackPtr s - BitVec.ofNat 64 offset) len
      (Extracted.textAddress + BitVec.ofNat 64 p) lenCode := by
  intro i hi j hj he
  have hs := P256.Proofs.Program.stack_sub_toNat hp.stack ho
  have hb := P256.Proofs.Program.stack_bounds hp.stack
  have hin : (Stack.region s 80).Contains
      (stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat := by
    apply memoryRegion_contains_add hp.stack.1 (len := len) _ _ hi
    · rw [hs]
      change (stackPtr s).toNat - 80 ≤ (stackPtr s).toNat-offset
      omega
    · rw [stack_region_end, hs]
      omega
  apply hp.avoids (Stack.region s 80) (by simp) _ hin
  left
  rw [he, add_ofNat_add_ofNat]
  exact inProgram_of_textOffset (p+j) (by omega)

omit [Bindings] in
theorem stack_store_frame (h : AgreesExcept (components s 0) s t)
    {offset len : Nat} (ho : 48 ≤ offset) (hb : offset ≤ 72) (hl : len ≤ offset-48)
    (he : AgreesExcept [.mem (stackPtr s - BitVec.ofNat 64 offset) len, .rip] t u) :
    AgreesExcept (components s 0) s u := by
  apply (h.trans he).widen
  · intro c hc hn
    simp only [List.mem_append] at hc
    rcases hc with hc | hc
    · exact hc
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · simp_all [Component.isMem]
      · simp [components, registers]
  · intro a c hc hv
    simp only [List.mem_append] at hc
    rcases hc with hc | hc
    · exact ⟨c, hc, hv⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · obtain ⟨i, hi, rfl⟩ := hv
        refine ⟨.mem (stackPtr s-72) 24, by simp [components], 72-offset+i, by omega, ?_⟩
        rw [BitVec.ofNat_add, ← BitVec.add_assoc]
        have heq : (72 : BitVec 64) = BitVec.ofNat 64 offset + BitVec.ofNat 64 (72-offset) := by
          rw [← BitVec.ofNat_add, Nat.add_sub_cancel' hb]
          rfl
        rw [heq, ← BitVec.sub_sub, BitVec.sub_add_cancel]
      · exact hv.elim

end P256.Proofs.Program.LimbSelect
