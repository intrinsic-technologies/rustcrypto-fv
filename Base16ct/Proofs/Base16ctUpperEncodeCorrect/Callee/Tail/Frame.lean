import Base16ct.Proofs.Base16ctUpperEncodeCorrect.Callee.Support

namespace Base16ct.Proofs.Base16ctUpperEncodeCorrect

open Base16ct.Spec.Program Prelude X86 X86.Machine X86Proofs

theorem tail_stack_sub_offset (sp : BitVec 64) {back budget : Nat} (hb : back ≤ budget) :
    sp - BitVec.ofNat 64 budget + BitVec.ofNat 64 (budget - back) = sp - BitVec.ofNat 64 back := by
  apply (BitVec.add_left_inj (BitVec.ofNat 64 back)).mp
  simp only [BitVec.sub_add_cancel, BitVec.add_assoc, ← BitVec.ofNat_add,
    Nat.sub_add_cancel hb]

theorem tail_stack_slots_apart (sp : BitVec 64) {back other count len : Nat}
    (hback : back ≤ 32) (hother : other ≤ 32) (hcount : count ≤ back)
    (hlen : len ≤ other) (hsep : other + count ≤ back ∨ back + len ≤ other) :
    RangeApart (sp - BitVec.ofNat 64 back) count (sp - BitVec.ofNat 64 other) len := by
  rw [← tail_stack_sub_offset sp hback, ← tail_stack_sub_offset sp hother]
  apply RangeApart.offsets
  · omega
  · omega
  · omega

theorem tail_read_of_store_frame {s t : RamState} {addr other : BitVec 64} {count n : Nat}
    (h : AgreesExcept [.mem addr count, .rip] s t)
    (ha : RangeApart addr count other (n / 8)) :
    (Operand.mem other : Operand n).read t = (Operand.mem other : Operand n).read s := by
  apply memLoad_congr
  intro i hi
  change (t.external[other + BitVec.ofNat 64 i]?).getD 0 =
    (s.external[other + BitVec.ofNat 64 i]?).getD 0
  rw [h.byte]
  intro c hc hcover
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · obtain ⟨j, hj, he⟩ := hcover
    exact ha j hj i hi he.symm
  · exact hcover


theorem tail_store_frame_widen (c : CallContext) {s t : RamState} {back count : Nat}
    (hb : back ≤ 24) (hc : count + 8 ≤ back)
    (h : AgreesExcept [.mem (stackPtr c.initial - BitVec.ofNat 64 back) count, .rip] s t) :
    AgreesExcept (calleeComponents c) s t := by
  apply h.widen
  · intro component hm hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · cases hn
    · simp [calleeComponents]
  · intro x component hm hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · obtain ⟨i, hi, he⟩ := hx
      refine ⟨.mem (stackPtr c.initial - 24) 16, by simp [calleeComponents],
        24 - back + i, by omega, ?_⟩
      rw [BitVec.ofNat_add, ← BitVec.add_assoc]
      exact he.trans (congrArg (fun a => a + BitVec.ofNat 64 i)
        (tail_stack_sub_offset (stackPtr c.initial) hb).symm)
    · exact False.elim hx

theorem tail_stack_code_apart (c : CallContext) {back count offset len : Nat}
    (hb : back ≤ 32) (hc : count ≤ back)
    (hcode : offset + len ≤ Extracted.textBytes.size) :
    RangeApart (stackPtr c.initial - BitVec.ofNat 64 back) count
      (Extracted.textAddress + BitVec.ofNat 64 offset) len := by
  obtain ⟨hstart, hend⟩ := stack_subrange_bounds c.valid.stack (by omega : back ≤ 160)
  exact rangeApart_text_of_avoids c.valid.stack.1 (stack_avoids_program c.valid.separation)
    hstart (by omega) hcode

theorem tail_output_of_store_frame (c : CallContext) {s t : RamState}
    {back count len : Nat} {f : Nat → UInt8} (hb : back ≤ 32) (hc : count ≤ back)
    (hl : len ≤ c.capacity)
    (h : AgreesExcept [.mem (stackPtr c.initial - BitVec.ofNat 64 back) count, .rip] s t)
    (hout : Bytes s.external (c.initial.regValue .rcx) len f) :
    Bytes t.external (c.initial.regValue .rcx) len f := by
  have hd : (Stack.region c.initial 160).Disjoint (outputRegion c.initial c.capacity) :=
    fun a hs ho => c.valid.separation.1 1 2 (by decide) a ho hs
  obtain ⟨hstart, hend⟩ := stack_subrange_bounds c.valid.stack (by omega : back ≤ 160)
  have ha : RangeApart (stackPtr c.initial - BitVec.ofNat 64 back) count
      (c.initial.regValue .rcx) len :=
    rangeApart_of_disjoint_subranges c.valid.stack.1 c.valid.outputInMemory.2.1 hd hstart (by omega)
      (Nat.le_refl _) (by change _ ≤ (c.initial.regValue .rcx).toNat + c.capacity; omega)
  apply hout.of_agreesExcept h
  intro i hi component hm hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  · obtain ⟨j, hj, he⟩ := hx
    exact ha j hj i hi he.symm
  · exact hx

end Base16ct.Proofs.Base16ctUpperEncodeCorrect
