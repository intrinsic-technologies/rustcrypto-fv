import P256.Proofs.Signing.Core.Iteration.Components.Constructor.Frame
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import P256.Proofs.Program.Pop
import X86Proofs.Instructions.Call.Triple

set_option autoImplicit false

open P256.Proofs.Program

namespace P256.Proofs.Signing.Core.Iteration.Components.Constructor.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem epilogue [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x109890 32 72 512) (state : Stage s t boundary)
    (rip : t.RIP = 0x109a1c) :
    ∃ u, CalleeResult s u boundary 72 512 ∧ u.external = t.external := by
  have code := programLoaded_codeIn state.loaded
  have hRead (offset : Nat) (ho : offset ≤ 512) :
      MemReadable t (stackPtr s - BitVec.ofNat 64 offset) 8 :=
    Program.readable_of_grow
      (Program.stack_sub_readable pre.stack ho (by omega)) state.allocated
  obtain ⟨t0, ha0, hr0, he0⟩ :=
    (mov_r64_r64_effect_step 0x109a1c 0x48 0xd8 (by simp [RexWPrefix]) (by decide)).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice code 0x9a1c [0x48, 0x89, 0xd8] (by decide) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9a1f (by decide)))
  change (movR64R64Effect 0x109a1c 0 3 t).Holds t t0 at he0
  have hm0 : t0.external = t.external := he0.agrees.external (by simp [Component.Covers])
  have hsp0 : stackPtr t0 = stackPtr s - 216 :=
    (he0.agrees.read (n := 64) (r := 4) (by simp)).trans state.rsp
  obtain ⟨t1, ha1, hr1, he1⟩ :=
    (add_r64_imm32_effect_step 0x109a1f 0x48 0xc4 192
      (by simp [RexWPrefix]) (by decide) (by decide)).advances hr0
      (programText_slice (code.of_external_eq hm0) 0x9a1f [0x48,0x81,0xc4,0xc0,0,0,0]
        (by decide) (by decide +kernel)) he0.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9a26 (by decide)))
  change (addR64Imm32Effect 0x109a1f 4 192 t0).Holds t0 t1 at he1
  have hm1 : t1.external = t.external :=
    (he1.agrees.external (by simp [Component.Covers])).trans hm0
  have hsp1 : stackPtr t1 = stackPtr s - 24 := by
    have hw : stackPtr t1 = stackPtr t0 + 192 := he1.writes
    rw [hw, hsp0]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have hread1 : MemReadable t1 (stackPtr t1) 8 := by
    rw [hsp1]
    exact (hRead 24 (by decide)).of_external_eq hm1
  obtain ⟨t2, ha2, hr2, he2⟩ :=
    (Program.pop_register_effect_step 0x109a26 3 (by decide)).advances hr1
      (programText_slice (code.of_external_eq hm1) 0x9a26 (encodePopR64 3)
        (by decide) (by decide +kernel)) ⟨he1.rip, hread1⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9a27 (by decide)))
  change (popR64Effect 0x109a26 1 3 t1).Holds t1 t2 at he2
  have hm2 : t2.external = t.external :=
    (he2.agrees.external (by simp [Component.Covers])).trans hm1
  have hsp2 : stackPtr t2 = stackPtr s - 16 := by
    have hw : stackPtr t2 = stackPtr t1 + 8 := he2.writes.2
    rw [hw, hsp1]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have hv2 : (Operand.reg 3 : Operand 64).read t2 = s.regValue .rbx := by
    have hw : (Operand.reg 3 : Operand 64).read t2 =
        (Operand.mem (stackPtr t1) : Operand 64).read t1 := he2.writes.1
    rw [hw, hsp1]
    change memLoad t1.external (stackPtr s - 24) 64 = _
    rw [hm1]
    exact state.savedRbx
  have hread2 : MemReadable t2 (stackPtr t2) 8 := by
    rw [hsp2]
    exact (hRead 16 (by decide)).of_external_eq hm2
  obtain ⟨t3, ha3, hr3, he3⟩ :=
    (Program.pop_register_effect_step 0x109a27 14 (by decide)).advances hr2
      (programText_slice (code.of_external_eq hm2) 0x9a27 (encodePopR64 14)
        (by decide) (by decide +kernel)) ⟨he2.rip, hread2⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9a29 (by decide)))
  change (popR64Effect 0x109a27 2 14 t2).Holds t2 t3 at he3
  have hm3 : t3.external = t.external :=
    (he3.agrees.external (by simp [Component.Covers])).trans hm2
  have hsp3 : stackPtr t3 = stackPtr s - 8 := by
    have hw : stackPtr t3 = stackPtr t2 + 8 := he3.writes.2
    rw [hw, hsp2]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have hv3 : (Operand.reg 14 : Operand 64).read t3 = s.regValue .r14 := by
    have hw : (Operand.reg 14 : Operand 64).read t3 =
        (Operand.mem (stackPtr t2) : Operand 64).read t2 := he3.writes.1
    rw [hw, hsp2]
    change memLoad t2.external (stackPtr s - 16) 64 = _
    rw [hm2]
    exact state.savedR14
  have hread3 : MemReadable t3 (stackPtr t3) 8 := by
    rw [hsp3]
    exact (hRead 8 (by decide)).of_external_eq hm3
  obtain ⟨t4, ha4, hr4, he4⟩ :=
    (Program.pop_register_effect_step 0x109a29 15 (by decide)).advances hr3
      (programText_slice (code.of_external_eq hm3) 0x9a29 (encodePopR64 15)
        (by decide) (by decide +kernel)) ⟨he3.rip, hread3⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9a2b (by decide)))
  change (popR64Effect 0x109a29 2 15 t3).Holds t3 t4 at he4
  have hm4 : t4.external = t.external :=
    (he4.agrees.external (by simp [Component.Covers])).trans hm3
  have hsp4 : stackPtr t4 = stackPtr s := by
    have hw : stackPtr t4 = stackPtr t3 + 8 := he4.writes.2
    rw [hw, hsp3, BitVec.sub_add_cancel]
  have hv4 : (Operand.reg 15 : Operand 64).read t4 = s.regValue .r15 := by
    have hw : (Operand.reg 15 : Operand 64).read t4 =
        (Operand.mem (stackPtr t3) : Operand 64).read t3 := he4.writes.1
    rw [hw, hsp3]
    change memLoad t3.external (stackPtr s - 8) 64 = _
    rw [hm3]
    exact state.savedR15
  have hread4 : MemReadable t4 (stackPtr t4) 8 := by
    rw [hsp4]
    simpa only [BitVec.sub_zero] using (hRead 0 (by decide)).of_external_eq hm4
  have htop4 : stackTop t4 = (returnBoundary s).rip := by
    rw [stackTop, hsp4]
    change memLoad t4.external (stackPtr s) 64 = _
    rw [hm4]
    exact state.returnAddress
  obtain ⟨u, ha5, hr5, he5⟩ := (ret_effect_step 0x109a2b).advances hr4
    (programText_slice (code.of_external_eq hm4) 0x9a2b [0xc3] (by decide) (by decide +kernel))
    ⟨⟨he4.rip, hread4⟩, htop4 ▸ Program.inProgram_low pre.returnInProgram⟩
    (by change stackTop t4 ≠ boundary.rip
        rw [htop4]
        exact boundary_ne_program pre.outerBoundary pre.returnInProgram)
  have hm5 : u.external = t.external :=
    (he5.agrees.external (by simp [Component.Covers])).trans hm4
  have hf := ((((he0.agrees.trans he1.agrees).trans he2.agrees).trans he3.agrees).trans he4.agrees).trans he5.agrees
  obtain ⟨fuel, hexec⟩ := state.execution
  refine ⟨u, ?_, hm5⟩
  refine ⟨⟨fuel + 6, ?_⟩, he5.rip.trans htop4, ?_,
    bindingsSupported_of_ready_agrees state.bindingsSupported hr5 hf,
    supportedMachine_of_ready_agrees state.machine hr5 hf, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (((((hexec.trans ha0).trans ha1).trans ha2).trans ha3).trans ha4).trans ha5
  · change stackPtr u = stackPtr s + 8
    have hw : stackPtr u = stackPtr t4 + 8 := he5.writes
    rw [hw, hsp4]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (Operand.reg 3 : Operand 64).read u = _
      rw [he5.agrees.read (by simp), he4.agrees.read (by simp), he3.agrees.read (by simp)]
      exact hv2
    · exact (hf.read (n := 64) (r := 5) (by simp)).trans state.rbp
    · exact (hf.read (n := 64) (r := 12) (by simp)).trans state.r12
    · exact (hf.read (n := 64) (r := 13) (by simp)).trans state.r13
    · change (Operand.reg 14 : Operand 64).read u = _
      rw [he5.agrees.read (by simp), he4.agrees.read (by simp)]
      exact hv3
    · change (Operand.reg 15 : Operand 64).read u = _
      rw [he5.agrees.read (by simp)]
      exact hv4
  · exact hf.directionFlagClear (by simp) state.directionFlag
  · exact (hf.mxcsr (by simp)).trans state.mxcsr
  · exact (hf.fcw (by simp)).trans state.fp87
  · intro address hout
    rw [hm5]
    exact state.frame address hout
  · intro address byte hfetch
    rw [hm5]
    exact state.loaded address byte hfetch
  · intro address ha
    rw [hm5]
    exact state.allocated address ha

end P256.Proofs.Signing.Core.Iteration.Components.Constructor.Finish
