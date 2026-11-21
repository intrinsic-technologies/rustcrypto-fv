import P256.Proofs.Verifying.Combination.Table.State
import P256.Proofs.Program.Code
import P256.Proofs.Program.Pop
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import X86Proofs.Instructions.Call.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Table

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program


theorem epilogue [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {cursor point : BitVec 64} (pre : TablePre s boundary cursor point)
    (state : FrameState s t cursor) (rip : t.RIP = 0x10b159)
    (rbx : t.regValue .rbx = s.regValue .rdi)
    (cursorValue : memLoad t.external cursor 64 = point+128)
    (execution : ∃ fuel, Advances boundary fuel s t) :
    ∃ u, TableResult s u boundary cursor point ∧ u.external = t.external := by
  have loaded := programLoaded_codeIn state.loaded
  have read (offset : Nat) (ho : offset ≤ 32) :
      MemReadable t (stackPtr s - BitVec.ofNat 64 offset) 8 :=
    readable_of_grow (stack_sub_readable pre.stack (by omega) (by omega)) state.allocated
  obtain ⟨t0, run0, ready0, effect0⟩ :=
    (mov_r64_r64_effect_step 0x10b159 0x48 0xd8 (by simp [RexWPrefix]) rfl).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice loaded 0xb159 _ (by decide) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xb15c (by decide)))
  change (movR64R64Effect 0x10b159 0 3 t).Holds t t0 at effect0
  have mem0 : t0.external = t.external := effect0.agrees.external (by simp [Component.Covers])
  have value0 : t0.regValue .rax = s.regValue .rdi :=
    (show t0.regValue .rax = t.regValue .rbx from effect0.writes).trans rbx
  have sp0 : stackPtr t0 = stackPtr s-1096 :=
    (effect0.agrees.read (n := 64) (r := 4) (by simp)).trans state.rsp
  obtain ⟨t1, run1, ready1, effect1⟩ :=
    (add_r64_imm32_effect_step 0x10b15c 0x48 0xc4 1064
      (by simp [RexWPrefix]) (by decide) (by decide)).advances ready0
      (programText_slice (loaded.of_external_eq mem0) 0xb15c _ (by decide) (by decide +kernel)) effect0.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xb163 (by decide)))
  change (addR64Imm32Effect 0x10b15c 4 1064 t0).Holds t0 t1 at effect1
  have mem1 : t1.external = t.external :=
    (effect1.agrees.external (by simp [Component.Covers])).trans mem0
  have sp1 : stackPtr t1 = stackPtr s-32 := by
    have h : stackPtr t1 = stackPtr t0+1064 := effect1.writes
    rw [h, sp0]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have read2 : MemReadable t1 (stackPtr t1) 8 := by
    rw [sp1]
    exact (read 32 (by decide)).of_external_eq mem1
  obtain ⟨t2, run2, ready2, effect2⟩ :=
    (pop_register_effect_step 0x10b163 3 (by decide)).advances ready1
      (programText_slice (loaded.of_external_eq mem1) 0xb163 _ (by decide) (by decide +kernel))
      ⟨effect1.rip, read2⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xb164 (by decide)))
  have mem2 : t2.external = t.external :=
    (effect2.agrees.external (by simp [Component.Covers])).trans mem1
  have sp2 : stackPtr t2 = stackPtr s-24 := by
    have h : stackPtr t2 = stackPtr t1+8 := effect2.writes.2
    rw [h, sp1]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have value2 : t2.regValue .rbx = s.regValue .rbx := by
    have h : t2.regValue .rbx = memLoad t1.external (stackPtr t1) 64 := effect2.writes.1
    rw [h, sp1, mem1]
    exact state.saved (.rbx, 32) (by simp [savedRegisters])
  have read3 : MemReadable t2 (stackPtr t2) 8 := by
    rw [sp2]
    exact (read 24 (by decide)).of_external_eq mem2
  obtain ⟨t3, run3, ready3, effect3⟩ :=
    (pop_register_effect_step 0x10b164 12 (by decide)).advances ready2
      (programText_slice (loaded.of_external_eq mem2) 0xb164 _ (by decide) (by decide +kernel))
      ⟨effect2.rip, read3⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xb166 (by decide)))
  have mem3 : t3.external = t.external :=
    (effect3.agrees.external (by simp [Component.Covers])).trans mem2
  have sp3 : stackPtr t3 = stackPtr s-16 := by
    have h : stackPtr t3 = stackPtr t2+8 := effect3.writes.2
    rw [h, sp2]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have value3 : t3.regValue .r12 = s.regValue .r12 := by
    have h : t3.regValue .r12 = memLoad t2.external (stackPtr t2) 64 := effect3.writes.1
    rw [h, sp2, mem2]
    exact state.saved (.r12, 24) (by simp [savedRegisters])
  have read4 : MemReadable t3 (stackPtr t3) 8 := by
    rw [sp3]
    exact (read 16 (by decide)).of_external_eq mem3
  obtain ⟨t4, run4, ready4, effect4⟩ :=
    (pop_register_effect_step 0x10b166 14 (by decide)).advances ready3
      (programText_slice (loaded.of_external_eq mem3) 0xb166 _ (by decide) (by decide +kernel))
      ⟨effect3.rip, read4⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xb168 (by decide)))
  have mem4 : t4.external = t.external :=
    (effect4.agrees.external (by simp [Component.Covers])).trans mem3
  have sp4 : stackPtr t4 = stackPtr s-8 := by
    have h : stackPtr t4 = stackPtr t3+8 := effect4.writes.2
    rw [h, sp3]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have value4 : t4.regValue .r14 = s.regValue .r14 := by
    have h : t4.regValue .r14 = memLoad t3.external (stackPtr t3) 64 := effect4.writes.1
    rw [h, sp3, mem3]
    exact state.saved (.r14, 16) (by simp [savedRegisters])
  have read5 : MemReadable t4 (stackPtr t4) 8 := by
    rw [sp4]
    exact (read 8 (by decide)).of_external_eq mem4
  obtain ⟨t5, run5, ready5, effect5⟩ :=
    (pop_register_effect_step 0x10b168 15 (by decide)).advances ready4
      (programText_slice (loaded.of_external_eq mem4) 0xb168 _ (by decide) (by decide +kernel))
      ⟨effect4.rip, read5⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xb16a (by decide)))
  have mem5 : t5.external = t.external :=
    (effect5.agrees.external (by simp [Component.Covers])).trans mem4
  have sp5 : stackPtr t5 = stackPtr s-0#64 := by
    have h : stackPtr t5 = stackPtr t4+8 := effect5.writes.2
    rw [h, sp4]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have value5 : t5.regValue .r15 = s.regValue .r15 := by
    have h : t5.regValue .r15 = memLoad t4.external (stackPtr t4) 64 := effect5.writes.1
    rw [h, sp4, mem4]
    exact state.saved (.r15, 8) (by simp [savedRegisters])
  have sp5' : stackPtr t5 = stackPtr s := by simpa only [BitVec.sub_zero] using sp5
  have read6 : MemReadable t5 (stackPtr t5) 8 := by
    rw [sp5']
    simpa only [BitVec.sub_zero] using (read 0 (by decide)).of_external_eq mem5
  have top : stackTop t5 = (returnBoundary s).rip := by
    change memLoad t5.external (stackPtr t5) 64 = memLoad s.external (stackPtr s) 64
    rw [sp5', mem5]
    exact state.returnAddress
  obtain ⟨u, run6, ready6, effect6⟩ := (ret_effect_step 0x10b16a).advances ready5
    (programText_slice (loaded.of_external_eq mem5) 0xb16a _ (by decide) (by decide +kernel))
    ⟨⟨effect5.rip, read6⟩, top ▸ P256.Proofs.Program.inProgram_low pre.returnInProgram⟩
    (by change stackTop t5 ≠ boundary.rip
        rw [top]
        exact boundary_ne_program pre.outerBoundary pre.returnInProgram)
  have frame := (((((effect0.agrees.trans effect1.agrees).trans effect2.agrees).trans effect3.agrees).trans effect4.agrees).trans effect5.agrees).trans effect6.agrees
  have memory : u.external = t.external :=
    (effect6.agrees.external (by simp [Component.Covers])).trans mem5
  have regs : ∀ r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15],
      u.regValue r = s.regValue r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (effect6.agrees.read (n := 64) (r := 3) (by simp)).trans ((effect5.agrees.read (n := 64) (r := 3) (by simp)).trans ((effect4.agrees.read (n := 64) (r := 3) (by simp)).trans ((effect3.agrees.read (n := 64) (r := 3) (by simp)).trans (value2))))
    · exact (frame.read (n := 64) (r := 5) (by simp)).trans state.rbp
    · exact (effect6.agrees.read (n := 64) (r := 12) (by simp)).trans ((effect5.agrees.read (n := 64) (r := 12) (by simp)).trans ((effect4.agrees.read (n := 64) (r := 12) (by simp)).trans (value3)))
    · exact (frame.read (n := 64) (r := 13) (by simp)).trans state.r13
    · exact (effect6.agrees.read (n := 64) (r := 14) (by simp)).trans ((effect5.agrees.read (n := 64) (r := 14) (by simp)).trans (value4))
    · exact (effect6.agrees.read (n := 64) (r := 15) (by simp)).trans (value5)
  obtain ⟨n, run⟩ := execution
  refine ⟨u, ⟨⟨n+7, ((((((run.trans run0).trans run1).trans run2).trans run3).trans run4).trans run5).trans run6⟩,
    effect6.rip.trans top, ?_,
    bindingsSupported_of_ready_agrees state.bindingsSupported ready6 frame,
    supportedMachine_of_ready_agrees state.machine ready6 frame,
    regs, frame.directionFlagClear (by simp) state.directionFlag,
    (frame.mxcsr (by simp)).trans state.mxcsr,
    (frame.fcw (by simp)).trans state.fp87,
    ?_, ?_, fun a ha => frame.grow a (state.allocated a ha), ?_, ?_⟩, memory⟩
  · change stackPtr u = stackPtr s+8
    have h : stackPtr u = stackPtr t5+8 := effect6.writes
    rw [h, sp5']
  · intro a ha
    rw [memory]
    exact state.frame a ha
  · intro a b hb
    rw [memory]
    exact state.loaded a b hb
  · rw [memory]
    exact cursorValue
  · exact (((((effect1.agrees.trans effect2.agrees).trans effect3.agrees).trans effect4.agrees).trans effect5.agrees).trans effect6.agrees).read (n := 64) (r := 0) (by simp) |>.trans value0

end P256.Proofs.Verifying.Combination.Table
