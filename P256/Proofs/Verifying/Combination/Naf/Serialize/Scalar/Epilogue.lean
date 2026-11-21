import P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar.State
import P256.Proofs.Program.Pop
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Call.Triple
import X86Proofs.Instructions.Add.Generated.Imm32.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar

open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Verifying.Combination.Naf

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Program (pop_register_effect_step readable_of_grow stack_sub_readable)

theorem epilogue [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {cursor point : BitVec 64} (pre : ScalarPre s boundary cursor point)
    (state : FrameState s t cursor) (rip : t.RIP = 0x10b35e)
    (rbx : t.regValue .rbx = s.regValue .rdi)
    (cursorValue : memLoad t.external cursor 64 = point+128)
    (execution : ∃ fuel, Advances boundary fuel s t) :
    ∃ u, ScalarResult s u boundary cursor point ∧ u.external = t.external := by
  have loaded := programLoaded_codeIn state.loaded
  have read (offset : Nat) (ho : offset ≤ 16) :
      MemReadable t (stackPtr s - BitVec.ofNat 64 offset) 8 :=
    readable_of_grow (stack_sub_readable pre.stack (by omega) (by omega)) state.allocated
  obtain ⟨t0, run0, ready0, effect0⟩ :=
    (mov_r64_r64_effect_step 0x10b35e 0x48 0xd8 (by simp [RexWPrefix]) rfl).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice loaded 0xb35e _ (by decide) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xb361 (by decide)))
  change (movR64R64Effect 0x10b35e 0 3 t).Holds t t0 at effect0
  have mem0 : t0.external = t.external := effect0.agrees.external (by simp [Component.Covers])
  have value0 : t0.regValue .rax = s.regValue .rdi :=
    (show t0.regValue .rax = t.regValue .rbx from effect0.writes).trans rbx
  have sp0 : stackPtr t0 = stackPtr s-360 :=
    (effect0.agrees.read (n := 64) (r := 4) (by simp)).trans state.rsp
  obtain ⟨t1, run1, ready1, effect1⟩ :=
    (add_r64_imm32_effect_step 0x10b361 0x48 0xc4 344
      (by simp [RexWPrefix]) (by decide) (by decide)).advances ready0
      (programText_slice (loaded.of_external_eq mem0) 0xb361 _ (by decide) (by decide +kernel)) effect0.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xb368 (by decide)))
  change (addR64Imm32Effect 0x10b361 4 344 t0).Holds t0 t1 at effect1
  have mem1 : t1.external = t.external :=
    (effect1.agrees.external (by simp [Component.Covers])).trans mem0
  have sp1 : stackPtr t1 = stackPtr s-16 := by
    have h : stackPtr t1 = stackPtr t0+344 := effect1.writes
    rw [h, sp0]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have read2 : MemReadable t1 (stackPtr t1) 8 := by
    rw [sp1]
    exact (read 16 (by decide)).of_external_eq mem1
  obtain ⟨t2, run2, ready2, effect2⟩ :=
    (pop_register_effect_step 0x10b368 3 (by decide)).advances ready1
      (programText_slice (loaded.of_external_eq mem1) 0xb368 _ (by decide) (by decide +kernel))
      ⟨effect1.rip, read2⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xb369 (by decide)))
  have mem2 : t2.external = t.external :=
    (effect2.agrees.external (by simp [Component.Covers])).trans mem1
  have sp2 : stackPtr t2 = stackPtr s-8 := by
    have h : stackPtr t2 = stackPtr t1+8 := effect2.writes.2
    rw [h, sp1]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have value2 : t2.regValue .rbx = s.regValue .rbx := by
    have h : t2.regValue .rbx = memLoad t1.external (stackPtr t1) 64 := effect2.writes.1
    rw [h, sp1, mem1]
    exact state.saved (.rbx, 16) (by simp [savedRegisters])
  have read3 : MemReadable t2 (stackPtr t2) 8 := by
    rw [sp2]
    exact (read 8 (by decide)).of_external_eq mem2
  obtain ⟨t3, run3, ready3, effect3⟩ :=
    (pop_register_effect_step 0x10b369 14 (by decide)).advances ready2
      (programText_slice (loaded.of_external_eq mem2) 0xb369 _ (by decide) (by decide +kernel))
      ⟨effect2.rip, read3⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xb36b (by decide)))
  have mem3 : t3.external = t.external :=
    (effect3.agrees.external (by simp [Component.Covers])).trans mem2
  have sp3 : stackPtr t3 = stackPtr s-0#64 := by
    have h : stackPtr t3 = stackPtr t2+8 := effect3.writes.2
    rw [h, sp2]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have value3 : t3.regValue .r14 = s.regValue .r14 := by
    have h : t3.regValue .r14 = memLoad t2.external (stackPtr t2) 64 := effect3.writes.1
    rw [h, sp2, mem2]
    exact state.saved (.r14, 8) (by simp [savedRegisters])
  have sp3' : stackPtr t3 = stackPtr s := by simpa only [BitVec.sub_zero] using sp3
  have read4 : MemReadable t3 (stackPtr t3) 8 := by
    rw [sp3']
    simpa only [BitVec.sub_zero] using (read 0 (by decide)).of_external_eq mem3
  have top : stackTop t3 = (returnBoundary s).rip := by
    change memLoad t3.external (stackPtr t3) 64 = memLoad s.external (stackPtr s) 64
    rw [sp3', mem3]
    exact state.returnAddress
  obtain ⟨u, run4, ready4, effect4⟩ := (ret_effect_step 0x10b36b).advances ready3
    (programText_slice (loaded.of_external_eq mem3) 0xb36b _ (by decide) (by decide +kernel))
    ⟨⟨effect3.rip, read4⟩, top ▸ P256.Proofs.Program.inProgram_low pre.returnInProgram⟩
    (by change stackTop t3 ≠ boundary.rip
        rw [top]
        exact boundary_ne_program pre.outerBoundary pre.returnInProgram)
  have frame := (((effect0.agrees.trans effect1.agrees).trans effect2.agrees).trans effect3.agrees).trans effect4.agrees
  have memory : u.external = t.external :=
    (effect4.agrees.external (by simp [Component.Covers])).trans mem3
  have regs : ∀ r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15],
      u.regValue r = s.regValue r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (effect4.agrees.read (n := 64) (r := 3) (by simp)).trans
        ((effect3.agrees.read (n := 64) (r := 3) (by simp)).trans value2)
    · exact (frame.read (n := 64) (r := 5) (by simp)).trans state.rbp
    · exact (frame.read (n := 64) (r := 12) (by simp)).trans state.r12
    · exact (frame.read (n := 64) (r := 13) (by simp)).trans state.r13
    · exact (effect4.agrees.read (n := 64) (r := 14) (by simp)).trans value3
    · exact (frame.read (n := 64) (r := 15) (by simp)).trans state.r15
  obtain ⟨n, run⟩ := execution
  refine ⟨u, ⟨⟨n+5, ((((run.trans run0).trans run1).trans run2).trans run3).trans run4⟩,
    effect4.rip.trans top, ?_, bindingsSupported_of_ready_agrees state.bindingsSupported ready4 frame, supportedMachine_of_ready_agrees state.machine ready4 frame,
    regs, frame.directionFlagClear (by simp) state.directionFlag,
      (frame.mxcsr (by simp)).trans state.mxcsr,
      (frame.fcw (by simp)).trans state.fp87,
    ?_, ?_, fun a ha => frame.grow a (state.allocated a ha), ?_, ?_⟩, memory⟩
  · change stackPtr u = stackPtr s+8
    have h : stackPtr u = stackPtr t3+8 := effect4.writes
    rw [h, sp3']
  · intro a ha
    rw [memory]
    exact state.frame a ha
  · intro a b hb
    rw [memory]
    exact state.loaded a b hb
  · rw [memory]
    exact cursorValue
  · exact (((effect1.agrees.trans effect2.agrees).trans effect3.agrees).trans effect4.agrees).read (n := 64) (r := 0) (by simp) |>.trans value0

end P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar
