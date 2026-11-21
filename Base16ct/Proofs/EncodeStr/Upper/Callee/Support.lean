import Base16ct.Proofs.EncodeStr.Upper.Callee.State

namespace Base16ct.Proofs.EncodeStr.Upper

open Base16ct.Spec.Program Prelude X86 X86.Machine X86Proofs

def calleeComponents (c : CallContext) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 4, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11,
   .flags, .rip, .mem (c.initial.regValue .rcx) c.writeLength,
   .mem (stackPtr c.initial - 24) 16]

theorem encoderComponents_avoids (c : CallContext) :
    ∀ x ∈ Extracted.programImage, ∀ component ∈ encoderComponents c.initial c.writeLength,
      ¬ component.Covers x.1 := by
  intro x hx component hc hcover
  have hp : InProgram x.1 := ⟨x.2, hx⟩
  simp only [encoderComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;> try exact False.elim hcover
  · have ho : (outputRegion c.initial c.capacity).Contains x.1.toNat := by
      apply contains_of_mem_covers c.valid.outputInMemory.2.1
      simpa only [outputRegion, registerRegion, BitVec.ofNat_toNat, BitVec.setWidth_eq] using (show Component.Covers (.mem (c.initial.regValue .rcx) c.capacity) _ from by
        obtain ⟨i, hi, he⟩ := hcover
        exact ⟨i, Nat.lt_of_lt_of_le hi c.writeLength_le_capacity, he⟩)
    exact c.valid.separation.2.1 _ (by simp) _ ho (.inl hp)
  · obtain ⟨i, hi, he⟩ := hcover
    obtain ⟨hstart, hend⟩ := stack_subrange_bounds c.valid.stack (used := 32) (by decide)
    apply stack_avoids_program c.valid.separation _ _ hp
    rw [he]
    exact contains_offset_of_subrange c.valid.stack.1 hstart (by omega) i hi

theorem RunInvariant.of_agrees [Bindings] (c : CallContext) {s t : RamState}
    (hs : RunInvariant c s) (hr : ReadyToStep t)
    (h : AgreesExcept (encoderComponents c.initial c.writeLength) s t) : RunInvariant c t := by
  refine ⟨hr, CodeIn.of_agreesExcept h (encoderComponents_avoids c) hs.code, ?_⟩
  exact (hs.agrees.trans h).mono (by simp)

theorem calleeComponents_widen (c : CallContext) {s t : RamState}
    (h : AgreesExcept (calleeComponents c) s t) :
    AgreesExcept (encoderComponents c.initial c.writeLength) s t := by
  apply h.widen
  · intro component hc hm
    simp only [calleeComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> simp_all [encoderComponents, Component.isMem]
  · intro x component hc hcover
    simp only [calleeComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> try exact False.elim hcover
    · exact ⟨_, by simp [encoderComponents], hcover⟩
    · obtain ⟨i, hi, he⟩ := hcover
      refine ⟨.mem (stackPtr c.initial - 32) 32, by simp [encoderComponents], 8 + i,
        by omega, ?_⟩
      rw [he, BitVec.ofNat_add]
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
      congr 1
      rw [← BitVec.add_assoc]
      rfl

theorem callee_output_store_widen (c : CallContext) {s t : RamState} {offset count : Nat}
    (hcap : 2 * c.input.length ≤ c.capacity)
    (hoff : offset + count ≤ 2 * c.input.length)
    (h : AgreesExcept [.mem (c.initial.regValue .rcx + BitVec.ofNat 64 offset) count,
      .rip] s t) : AgreesExcept (calleeComponents c) s t := by
  apply h.widen
  · intro component hc hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · contradiction
    · simp [calleeComponents]
  · intro x component hc hcover
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · obtain ⟨i, hi, he⟩ := hcover
      refine ⟨.mem (c.initial.regValue .rcx) c.writeLength, by simp [calleeComponents],
        offset + i, by simpa only [CallContext.writeLength, ite_eq_left hcap] using (show offset + i < 2 * c.input.length by omega), ?_⟩
      simpa only [BitVec.ofNat_add, BitVec.add_assoc] using he
    · exact False.elim hcover

theorem output_store_widen (c : CallContext) {s t : RamState} {offset count : Nat}
    (hcap : 2 * c.input.length ≤ c.capacity)
    (hoff : offset + count ≤ 2 * c.input.length)
    (h : AgreesExcept [.mem (c.initial.regValue .rcx + BitVec.ofNat 64 offset) count,
      .rip] s t) : AgreesExcept (encoderComponents c.initial c.writeLength) s t :=
  calleeComponents_widen c (callee_output_store_widen c hcap hoff h)

theorem stack_store_widen (c : CallContext) {s t : RamState} {back count : Nat}
    (hb : back ≤ 32) (hc : count ≤ back)
    (h : AgreesExcept [.mem (stackPtr c.initial - BitVec.ofNat 64 back) count,
      .rip] s t) : AgreesExcept (encoderComponents c.initial c.writeLength) s t := by
  have hoff : stackPtr c.initial - BitVec.ofNat 64 back =
      stackPtr c.initial - 32 + BitVec.ofNat 64 (32 - back) := by
    rw [← BitVec.ofNat_sub_ofNat_of_le 32 back (by omega) hb]
    simp only [BitVec.sub_eq_add_neg]
    rw [← BitVec.add_assoc, BitVec.add_assoc (stackPtr c.initial)]
    change _ = stackPtr c.initial + 0 + -BitVec.ofNat 64 back
    exact (congrArg (fun x : BitVec 64 => x + -BitVec.ofNat 64 back)
      (BitVec.add_zero (stackPtr c.initial))).symm
  apply h.widen
  · intro component hm hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · contradiction
    · simp [encoderComponents]
  · intro x component hm hcover
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · obtain ⟨i, hi, he⟩ := hcover
      refine ⟨.mem (stackPtr c.initial - 32) 32, by simp [encoderComponents],
        32 - back + i, by omega, ?_⟩
      rw [he, hoff, BitVec.ofNat_add, BitVec.add_assoc]
    · exact False.elim hcover

theorem RunInvariant.of_callee_agrees [Bindings] (c : CallContext) {s t : RamState}
    (hs : RunInvariant c s) (hr : ReadyToStep t)
    (h : AgreesExcept (calleeComponents c) s t) : RunInvariant c t :=
  hs.of_agrees c hr (calleeComponents_widen c h)

theorem callee_return_apart (c : CallContext) :
    RangeApart (stackPtr c.initial - 24) 16 (stackPtr c.initial - 32) 8 := by
  have hsp : 32 ≤ (stackPtr c.initial).toNat := c.stack32.2.2.1
  have hlow := (stack_return_readable c.valid.stack).low
  have h24 : (stackPtr c.initial - 24).toNat = (stackPtr c.initial).toNat - 24 := by
    rw [BitVec.toNat_sub_of_le (by change 24 ≤ (stackPtr c.initial).toNat; omega)]
    rfl
  have h32 : (stackPtr c.initial - 32).toNat = (stackPtr c.initial).toNat - 32 := by
    rw [BitVec.toNat_sub_of_le (by change 32 ≤ (stackPtr c.initial).toNat; omega)]
    rfl
  apply RangeApart.of_toNat
  · rw [h24]; omega
  · rw [h32]; omega
  · right; rw [h24, h32]; omega

theorem calleeComponents_return (c : CallContext) {s t : RamState}
    (h : AgreesExcept (calleeComponents c) s t) :
    (Operand.mem (stackPtr c.initial - 32) : Operand 64).read t =
      (Operand.mem (stackPtr c.initial - 32) : Operand 64).read s := by
  apply memLoad_congr
  intro i hi
  change (t.external[(stackPtr c.initial - 32) + BitVec.ofNat 64 i]?).getD 0 =
    (s.external[(stackPtr c.initial - 32) + BitVec.ofNat 64 i]?).getD 0
  congr 1
  apply h.byte
  intro component hc hcover
  simp only [calleeComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> try exact False.elim hcover
  · have ho : (outputRegion c.initial c.capacity).Contains
        ((stackPtr c.initial - 32) + BitVec.ofNat 64 i).toNat := by
      apply contains_of_mem_covers c.valid.outputInMemory.2.1
      simpa only [outputRegion, registerRegion, BitVec.ofNat_toNat, BitVec.setWidth_eq] using (show Component.Covers (.mem (c.initial.regValue .rcx) c.capacity) _ from by
        obtain ⟨i, hi, he⟩ := hcover
        exact ⟨i, Nat.lt_of_lt_of_le hi c.writeLength_le_capacity, he⟩)
    have hd : (outputRegion c.initial c.capacity).Disjoint (Stack.region c.initial 160) :=
      c.valid.separation.1 1 2 (by decide)
    apply hd _ ho
    obtain ⟨hstart, hend⟩ := stack_subrange_bounds c.valid.stack (used := 32) (by decide)
    exact contains_offset_of_subrange c.valid.stack.1 hstart (by omega) i hi
  · obtain ⟨j, hj, he⟩ := hcover
    exact callee_return_apart c j hj i hi he.symm

theorem callee_savedRbx_apart (c : CallContext) :
    RangeApart (stackPtr c.initial - 24) 16 (stackPtr c.initial - 8) 8 := by
  have hsp : 32 ≤ (stackPtr c.initial).toNat := c.stack32.2.2.1
  have hlow := (stack_return_readable c.valid.stack).low
  have h24 : (stackPtr c.initial - 24).toNat = (stackPtr c.initial).toNat - 24 := by
    rw [BitVec.toNat_sub_of_le (by change 24 ≤ (stackPtr c.initial).toNat; omega)]
    rfl
  have h8 : (stackPtr c.initial - 8).toNat = (stackPtr c.initial).toNat - 8 := by
    rw [BitVec.toNat_sub_of_le (by change 8 ≤ (stackPtr c.initial).toNat; omega)]
    rfl
  apply RangeApart.of_toNat
  · rw [h24]; omega
  · rw [h8]; omega
  · left; rw [h24, h8]; omega

theorem calleeComponents_savedRbx (c : CallContext) {s t : RamState}
    (h : AgreesExcept (calleeComponents c) s t) :
    (Operand.mem (stackPtr c.initial - 8) : Operand 64).read t =
      (Operand.mem (stackPtr c.initial - 8) : Operand 64).read s := by
  apply memLoad_congr
  intro i hi
  change (t.external[(stackPtr c.initial - 8) + BitVec.ofNat 64 i]?).getD 0 =
    (s.external[(stackPtr c.initial - 8) + BitVec.ofNat 64 i]?).getD 0
  congr 1
  apply h.byte
  intro component hc hcover
  simp only [calleeComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> try exact False.elim hcover
  · have ho : (outputRegion c.initial c.capacity).Contains
        ((stackPtr c.initial - 8) + BitVec.ofNat 64 i).toNat := by
      apply contains_of_mem_covers c.valid.outputInMemory.2.1
      simpa only [outputRegion, registerRegion, BitVec.ofNat_toNat, BitVec.setWidth_eq] using (show Component.Covers (.mem (c.initial.regValue .rcx) c.capacity) _ from by
        obtain ⟨i, hi, he⟩ := hcover
        exact ⟨i, Nat.lt_of_lt_of_le hi c.writeLength_le_capacity, he⟩)
    have hd : (outputRegion c.initial c.capacity).Disjoint (Stack.region c.initial 160) :=
      c.valid.separation.1 1 2 (by decide)
    apply hd _ ho
    obtain ⟨hstart, hend⟩ := stack_subrange_bounds c.valid.stack (used := 8) (by decide)
    exact contains_offset_of_subrange c.valid.stack.1 hstart (by omega) i hi
  · obtain ⟨j, hj, he⟩ := hcover
    exact callee_savedRbx_apart c j hj i hi he.symm

theorem calleeComponents_rbx (c : CallContext) {s t : RamState}
    (h : AgreesExcept (calleeComponents c) s t) :
    t.regValue .rbx = s.regValue .rbx := by
  exact h.agree (.reg 3) (by simp [calleeComponents]) rfl

theorem callee_ne_return (c : CallContext) (offset : Nat)
    (h : offset < Extracted.textBytes.size) :
    Extracted.textAddress + BitVec.ofNat 64 offset ≠ (returnBoundary c.initial).rip :=
  text_address_ne_return (returnBoundary_valid c.valid.stack c.valid.returnAddress).2 offset h

end Base16ct.Proofs.EncodeStr.Upper
