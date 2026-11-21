import P256.Proofs.Generate.Scalar.State
import X86Proofs.Instructions.Call.Triple
import P256.Proofs.Program.Pop
import X86Proofs.Instructions.Add.Generated.Imm8.Triple

set_option autoImplicit false

namespace P256.Proofs.Generate.Scalar

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program

theorem scalar_return [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (state : State s t) (rip : t.RIP = 0x112fc0)
    (rsp : stackPtr t = stackPtr s - 56) (execution : ∃ n, Advances boundary n s t) :
    ∃ u, CalleeResult s u boundary 33 72 ∧ u.external = t.external ∧
      u.regValue .rax = t.regValue .rax := by
  have code := programLoaded_codeIn state.loaded
  have read (offset : Nat) (bound : offset ≤ 72) :
      MemReadable t (stackPtr s - BitVec.ofNat 64 offset) 8 :=
    readable_of_grow (stack_sub_readable pre.stack bound (by omega)) state.allocated
  obtain ⟨t1, a1, r1, e1⟩ :=
    (add_r64_imm8_effect_step 0x112fc0 0x48 0xc4 16 (by simp [RexWPrefix]) rfl rfl).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice code 0x12fc0 [0x48,0x83,0xc4,0x10] (by decide) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x12fc4 (by decide)))
  change (addR64Imm8Effect 0x112fc0 4 16 t).Holds t t1 at e1
  have m1 : t1.external = t.external := e1.agrees.external (by simp [Component.Covers])
  have sp1 : stackPtr t1 = stackPtr s - 40 := by
    have w : stackPtr t1 = stackPtr t + 16 := e1.writes
    rw [w, rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have read1 : MemReadable t1 (stackPtr t1) 8 := by
    rw [sp1]
    exact (read 40 (by decide)).of_external_eq m1
  obtain ⟨t2, a2, r2, e2⟩ :=
    (pop_register_effect_step 0x112fc4 3 (by decide)).advances r1
      (programText_slice (code.of_external_eq m1) 0x12fc4 (encodePopR64 3)
        (by decide) (by decide +kernel)) ⟨e1.rip, read1⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x12fc5 (by decide)))
  change (popR64Effect 0x112fc4 1 3 t1).Holds t1 t2 at e2
  have m2 : t2.external = t.external := (e2.agrees.external (by simp [Component.Covers])).trans m1
  have sp2 : stackPtr t2 = stackPtr s - 32 := by
    have w : stackPtr t2 = stackPtr t1 + 8 := e2.writes.2
    rw [w, sp1]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have v2 : t2.regValue .rbx = s.regValue .rbx := by
    have w : t2.regValue .rbx = memLoad t1.external (stackPtr t1) 64 := e2.writes.1
    rw [w, sp1, m1]
    exact state.saved (.rbx, 40) (by simp [savedRegisters])
  have read2 : MemReadable t2 (stackPtr t2) 8 := by
    rw [sp2]
    exact (read 32 (by decide)).of_external_eq m2
  obtain ⟨t3, a3, r3, e3⟩ :=
    (pop_register_effect_step 0x112fc5 12 (by decide)).advances r2
      (programText_slice (code.of_external_eq m2) 0x12fc5 (encodePopR64 12)
        (by decide) (by decide +kernel)) ⟨e2.rip, read2⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x12fc7 (by decide)))
  change (popR64Effect 0x112fc5 2 12 t2).Holds t2 t3 at e3
  have m3 : t3.external = t.external := (e3.agrees.external (by simp [Component.Covers])).trans m2
  have sp3 : stackPtr t3 = stackPtr s - 24 := by
    have w : stackPtr t3 = stackPtr t2 + 8 := e3.writes.2
    rw [w, sp2]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have v3 : t3.regValue .r12 = s.regValue .r12 := by
    have w : t3.regValue .r12 = memLoad t2.external (stackPtr t2) 64 := e3.writes.1
    rw [w, sp2, m2]
    exact state.saved (.r12, 32) (by simp [savedRegisters])
  have read3 : MemReadable t3 (stackPtr t3) 8 := by
    rw [sp3]
    exact (read 24 (by decide)).of_external_eq m3
  obtain ⟨t4, a4, r4, e4⟩ :=
    (pop_register_effect_step 0x112fc7 13 (by decide)).advances r3
      (programText_slice (code.of_external_eq m3) 0x12fc7 (encodePopR64 13)
        (by decide) (by decide +kernel)) ⟨e3.rip, read3⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x12fc9 (by decide)))
  change (popR64Effect 0x112fc7 2 13 t3).Holds t3 t4 at e4
  have m4 : t4.external = t.external := (e4.agrees.external (by simp [Component.Covers])).trans m3
  have sp4 : stackPtr t4 = stackPtr s - 16 := by
    have w : stackPtr t4 = stackPtr t3 + 8 := e4.writes.2
    rw [w, sp3]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have v4 : t4.regValue .r13 = s.regValue .r13 := by
    have w : t4.regValue .r13 = memLoad t3.external (stackPtr t3) 64 := e4.writes.1
    rw [w, sp3, m3]
    exact state.saved (.r13, 24) (by simp [savedRegisters])
  have read4 : MemReadable t4 (stackPtr t4) 8 := by
    rw [sp4]
    exact (read 16 (by decide)).of_external_eq m4
  obtain ⟨t5, a5, r5, e5⟩ :=
    (pop_register_effect_step 0x112fc9 14 (by decide)).advances r4
      (programText_slice (code.of_external_eq m4) 0x12fc9 (encodePopR64 14)
        (by decide) (by decide +kernel)) ⟨e4.rip, read4⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x12fcb (by decide)))
  change (popR64Effect 0x112fc9 2 14 t4).Holds t4 t5 at e5
  have m5 : t5.external = t.external := (e5.agrees.external (by simp [Component.Covers])).trans m4
  have sp5 : stackPtr t5 = stackPtr s - 8 := by
    have w : stackPtr t5 = stackPtr t4 + 8 := e5.writes.2
    rw [w, sp4]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have v5 : t5.regValue .r14 = s.regValue .r14 := by
    have w : t5.regValue .r14 = memLoad t4.external (stackPtr t4) 64 := e5.writes.1
    rw [w, sp4, m4]
    exact state.saved (.r14, 16) (by simp [savedRegisters])
  have read5 : MemReadable t5 (stackPtr t5) 8 := by
    rw [sp5]
    exact (read 8 (by decide)).of_external_eq m5
  obtain ⟨t6, a6, r6, e6⟩ :=
    (pop_register_effect_step 0x112fcb 15 (by decide)).advances r5
      (programText_slice (code.of_external_eq m5) 0x12fcb (encodePopR64 15)
        (by decide) (by decide +kernel)) ⟨e5.rip, read5⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x12fcd (by decide)))
  change (popR64Effect 0x112fcb 2 15 t5).Holds t5 t6 at e6
  have m6 : t6.external = t.external := (e6.agrees.external (by simp [Component.Covers])).trans m5
  have sp6 : stackPtr t6 = stackPtr s - 0 := by
    have w : stackPtr t6 = stackPtr t5 + 8 := e6.writes.2
    rw [w, sp5]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have v6 : t6.regValue .r15 = s.regValue .r15 := by
    have w : t6.regValue .r15 = memLoad t5.external (stackPtr t5) 64 := e6.writes.1
    rw [w, sp5, m5]
    exact state.saved (.r15, 8) (by simp [savedRegisters])
  have sp : stackPtr t6 = stackPtr s := by simpa using sp6
  have top : stackTop t6 = (returnBoundary s).rip := by
    rw [stackTop, sp]
    change memLoad t6.external (stackPtr s) 64 = _
    rw [m6]
    exact state.returnAddress
  obtain ⟨u, a7, r7, e7⟩ := (ret_effect_step 0x112fcd).advances r6
    (programText_slice (code.of_external_eq m6) 0x12fcd [0xc3] (by decide) (by decide +kernel))
    ⟨⟨e6.rip, by rw [sp]; simpa using (read 0 (by decide)).of_external_eq m6⟩,
      top ▸ inProgram_low pre.returnInProgram⟩
    (by change stackTop t6 ≠ boundary.rip
        rw [top]
        exact boundary_ne_program pre.outerBoundary pre.returnInProgram)
  have memory : u.external = t.external := (e7.agrees.external (by simp [Component.Covers])).trans m6
  have ag := (((((e1.agrees.trans e2.agrees).trans e3.agrees).trans e4.agrees).trans e5.agrees).trans e6.agrees).trans e7.agrees
  refine ⟨u, ?_, memory, ag.read (n := 64) (r := 0) (by simp)⟩
  refine ⟨?_, e7.rip.trans top, ?_, bindingsSupported_of_ready_agrees state.bindingsSupported r7 ag,
    supportedMachine_of_ready_agrees state.machine r7 ag, ?_,
    ag.directionFlagClear (by simp) state.directionFlag,
    (ag.mxcsr (by simp)).trans state.mxcsr, (ag.fcw (by simp)).trans state.fp87,
    ?_, ?_, fun a ha => ag.grow a (state.allocated a ha)⟩
  · obtain ⟨n, run⟩ := execution
    exact ⟨n+7, run.trans ((((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans a7)⟩
  · change stackPtr u = stackPtr s + 8
    have w : stackPtr u = stackPtr t6 + 8 := e7.writes
    rw [w, sp]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (((((e3.agrees.trans e4.agrees).trans e5.agrees).trans e6.agrees).trans e7.agrees).read (n := 64) (r := 3) (by simp)).trans v2
    · exact (ag.read (n := 64) (r := 5) (by simp)).trans state.rbp
    · exact ((((e4.agrees.trans e5.agrees).trans e6.agrees).trans e7.agrees).read (n := 64) (r := 12) (by simp)).trans v3
    · exact (((e5.agrees.trans e6.agrees).trans e7.agrees).read (n := 64) (r := 13) (by simp)).trans v4
    · exact ((e6.agrees.trans e7.agrees).read (n := 64) (r := 14) (by simp)).trans v5
    · exact (e7.agrees.read (n := 64) (r := 15) (by simp)).trans v6
  · intro a ha
    rw [memory]
    exact state.frame a ha
  · intro a b hb
    rw [memory]
    exact state.loaded a b hb

end P256.Proofs.Generate.Scalar
