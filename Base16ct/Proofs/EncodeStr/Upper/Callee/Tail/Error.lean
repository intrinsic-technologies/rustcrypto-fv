import Base16ct.Proofs.EncodeStr.Upper.Callee.Tail.Frame
import Base16ct.Proofs.EncodeStr.Upper.Callee.Memory
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Call.Triple

namespace Base16ct.Proofs.EncodeStr.Upper

open Base16ct.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem callee_error_tail [Bindings] (c : CallContext) {s : RamState}
    (hc : ¬ 2 * c.input.length ≤ c.capacity) (hs : ErrorState c s) :
    ∃ t, Advances (returnBoundary c.initial) 3 s t ∧ RunInvariant c t ∧ CalleeExit c t := by
  have addr1 : storeAddrAt 0x1005cc (.base 0 (.d8 8)) (3 + (AddrMode.base 0 (.d8 8)).tail.length) s =
      stackPtr c.initial - 16 := by
    change (Operand.reg 0 : Operand 64).read s + 8 = _
    change s.regValue .rax + 8 = _
    rw [hs.result]
    simp [BitVec.sub_eq_add_neg, BitVec.add_assoc]
  have writable1 : MemWritable s (stackPtr c.initial - 16) 1 := by
    have h : MemWritable s (stackPtr c.initial - 16) 8 :=
      hs.invariant.stack_writable c 16 (by decide) (by decide)
    exact ⟨by have := h.low; omega,
      fun i hi => h.mem i (by omega), h.tables.sub (Nat.le_refl _) (by omega)⟩
  obtain ⟨s1, run1, ready1, e1⟩ :=
    (mov_m8_imm8_effect_step 0x1005cc (.base 0 (.d8 8))
      (by unfold AddrMode.Valid; decide +kernel) rfl rfl 1).advances hs.invariant.ready
      (by exact program_text_slice hs.invariant.code 0x5cc 4 (by decide +kernel))
      ⟨hs.rip, by simpa only [addr1] using writable1,
        by
          rw [addr1]
          exact tail_stack_code_apart c (back := 16) (count := 1)
            (offset := 0x5cc) (len := 4) (by decide) (by decide) (by decide +kernel)⟩
      (by exact callee_ne_return c 0x5d0 (by decide +kernel))
  have frame1 : AgreesExcept [.mem (stackPtr c.initial - 16) 1, .rip] s s1 := by
    simpa only [movM8Imm8Effect_components, addr1] using e1.agrees
  have inv1 := hs.invariant.of_callee_agrees c ready1
    (tail_store_frame_widen c (back := 16) (by decide) (by decide) frame1)
  have rax1 : s1.regValue .rax = stackPtr c.initial - 24 :=
    (frame1.read (n := 64) (r := 0) (by simp)).trans hs.result
  have rsp1 : stackPtr s1 = stackPtr c.initial - 32 :=
    (frame1.read (n := 64) (r := 4) (by simp)).trans hs.rsp
  have err1 : (Operand.mem (stackPtr c.initial - 16) : Operand 8).read s1 = 1 := by
    simpa only [movM8Imm8Effect, storeEffect, addr1, Write.AllHold] using e1.writes
  have ret1 : (Operand.mem (stackPtr c.initial - 32) : Operand 64).read s1 = 0x100476 :=
    (tail_read_of_store_frame frame1
      (tail_stack_slots_apart _ (back := 16) (other := 32)
        (by decide) (by decide) (by decide) (by decide) (by decide))).trans hs.returnAddress
  have addr2 : storeAddrAt 0x1005d0 (.base 0 .none) (7 + (AddrMode.base 0 .none).tail.length) s1 =
      stackPtr c.initial - 24 := by
    change s1.regValue .rax + 0 = _
    simpa using rax1
  obtain ⟨s2, run2, ready2, e2⟩ :=
    (mov_m64_imm32_effect_step 0x1005d0 0x48 (by unfold RexWPrefix; decide +kernel)
      (.base 0 .none) (by unfold AddrMode.Valid; decide +kernel) rfl rfl 0).advances ready1
      (by exact program_text_slice inv1.code 0x5d0 7 (by decide +kernel))
      ⟨e1.rip, by rw [addr2]; exact
        inv1.stack_writable c 24 (by decide) (by decide),
        by
          rw [addr2]
          exact tail_stack_code_apart c (back := 24) (count := 8)
            (offset := 0x5d0) (len := 7) (by decide) (by decide) (by decide +kernel)⟩
      (by exact callee_ne_return c 0x5d7 (by decide +kernel))
  have frame2 : AgreesExcept [.mem (stackPtr c.initial - 24) 8, .rip] s1 s2 := by
    simpa only [movM64Imm32Effect_components, addr2] using e2.agrees
  have inv2 := inv1.of_callee_agrees c ready2
    (tail_store_frame_widen c (back := 24) (by decide) (by decide) frame2)
  have rsp2 : stackPtr s2 = stackPtr c.initial - 32 :=
    (frame2.read (n := 64) (r := 4) (by simp)).trans rsp1
  have zero2 : (Operand.mem (stackPtr c.initial - 24) : Operand 64).read s2 = 0 := by
    have h : (Operand.mem (stackPtr c.initial - 24) : Operand 64).read s2 =
        (0 : BitVec 32).signExtend 64 := by
      simpa only [movM64Imm32Effect, storeEffect, addr2, Write.AllHold] using e2.writes
    simpa using h
  have err2 : (Operand.mem (stackPtr c.initial - 16) : Operand 8).read s2 = 1 :=
    (tail_read_of_store_frame frame2
      (tail_stack_slots_apart _ (back := 24) (other := 16)
        (by decide) (by decide) (by decide) (by decide) (by decide))).trans err1
  have ret2 : (Operand.mem (stackPtr c.initial - 32) : Operand 64).read s2 = 0x100476 :=
    (tail_read_of_store_frame frame2
      (tail_stack_slots_apart _ (back := 24) (other := 32)
        (by decide) (by decide) (by decide) (by decide) (by decide))).trans ret1
  have top2 : stackTop s2 = 0x100476 := by
    change (Operand.mem (stackPtr s2) : Operand 64).read s2 = _
    rw [rsp2]
    exact ret2
  obtain ⟨t, run3, ready3, e3⟩ := (ret_effect_step 0x1005d7).advances ready2
    (by exact program_text_slice inv2.code 0x5d7 1 (by decide +kernel))
    ⟨⟨e2.rip, by rw [rsp2]; exact
      inv2.stack_readable c 32 8 (by decide) (by decide)⟩,
      by rw [top2]; decide +kernel⟩
    (by change stackTop s2 ≠ _; rw [top2]; exact callee_ne_return c 0x476 (by decide +kernel))
  have inv3 := inv2.of_agrees c ready3
    (e3.agrees.mono (by simp [encoderComponents]))
  have mem3 : t.external = s2.external := e3.agrees.external (by simp [Component.Covers])
  refine ⟨t, (run1.trans run2).trans run3, inv3, e3.rip.trans top2, ?_, ?_, ?_, ?_⟩
  · have h : stackPtr t = stackPtr s2 + 8 := e3.writes
    rw [h, rsp2]
    simp [BitVec.sub_eq_add_neg, BitVec.add_assoc]
  · rw [ite_eq_right hc]
    change memLoad t.external (stackPtr c.initial - 24) 64 = 0 ∧
      memLoad t.external (stackPtr c.initial - 16) 8 = 1
    rw [mem3]
    exact ⟨zero2, err2⟩
  · exact (((frame1.trans frame2).trans e3.agrees).read (n := 64) (r := 3) (by simp)).trans hs.rbx
  · have q := (tail_store_frame_widen c (back := 16) (by decide) (by decide) frame1).trans
        (tail_store_frame_widen c (back := 24) (by decide) (by decide) frame2)
    change memLoad t.external _ 64 = _
    rw [mem3]
    exact (calleeComponents_savedRbx c (q.mono (by simp))).trans hs.savedRbx

end Base16ct.Proofs.EncodeStr.Upper
