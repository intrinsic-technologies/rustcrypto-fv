import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Entry
import P256.Proofs.Program.Pop
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.Call.Triple

set_option autoImplicit false

open P256.Proofs.Program (CalleePre CalleeResult boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice supportedMachine_of_ready_agrees readyToStep bindingsSupported_of_ready_agrees)

open P256.Proofs.Program

namespace P256.Proofs.Sec1.SquareRoot.Square.Reduction

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem epilogue [bindings : Bindings] {s t : RamState}
    {boundary : ReturnBoundary}
    (pre : ReductionPre s boundary)
    (state : ScalarFrame.FrameState s t 32 112 112)
    (execution : ∃ fuel, Advances boundary fuel s t)
    (rip : t.RIP = 0x1137a3) :
    ∃ u, CalleeResult s u boundary 32 112 ∧ u.external = t.external := by
  have code := programLoaded_codeIn state.loaded
  have hRead (offset : Nat) (ho : offset ≤ 112) :
      MemReadable t (stackPtr s - BitVec.ofNat 64 offset) 8 :=
    P256.Proofs.Program.readable_of_grow (P256.Proofs.Program.stack_sub_readable pre.stack ho (by omega)) state.allocated
  have hc1 : CodeIn (codeRange 0x1137a3 [0x48, 0x83, 0xc4, 0x40]) t :=
    programText_slice code 0x137a3 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t1, ha1, hr1, he1⟩ :=
    (add_r64_imm8_effect_step 0x1137a3 0x48 0xc4 64
      (by simp [RexWPrefix]) (by decide) (by decide)).advances
      (readyToStep state.machine state.bindingsSupported) hc1 rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x137a7 (by decide)))
  change (addR64Imm8Effect 0x1137a3 4 64 t).Holds t t1 at he1
  have hm1 : t1.external = t.external := he1.agrees.external (by simp [Component.Covers])
  have hsp1 : stackPtr t1 = stackPtr s - 48 := by
    have hw : stackPtr t1 = stackPtr t + 64 := he1.writes
    rw [hw, state.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have hread1 : MemReadable t1 (stackPtr t1) 8 := by
    rw [hsp1]
    exact (hRead 48 (by decide)).of_external_eq hm1
  have hc2 : CodeIn (codeRange 0x1137a7 (encodePopR64 3)) t1 :=
    programText_slice (code.of_external_eq hm1) 0x137a7 _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨t2, ha2, hr2, he2⟩ :=
    (P256.Proofs.Program.pop_register_effect_step 0x1137a7 3 (by decide)).advances hr1 hc2
      ⟨he1.rip, hread1⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x137a8 (by decide)))
  change (popR64Effect 0x1137a7 1 3 t1).Holds t1 t2 at he2
  have hm2 : t2.external = t.external :=
    (he2.agrees.external (by simp [Component.Covers])).trans hm1
  have hsp2 : stackPtr t2 = stackPtr s - 40 := by
    have hw : stackPtr t2 = stackPtr t1 + 8 := he2.writes.2
    rw [hw, hsp1]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have hv2 : (Operand.reg 3 : Operand 64).read t2 = s.regValue .rbx := by
    have hw : (Operand.reg 3 : Operand 64).read t2 =
        (Operand.mem (stackPtr t1) : Operand 64).read t1 := he2.writes.1
    rw [hw, hsp1]
    change memLoad t1.external (stackPtr s - 48) 64 = _
    rw [hm1]
    exact state.saved (.rbx, 48) (by simp [P256.Proofs.Program.savedRegisters])
  have hread2 : MemReadable t2 (stackPtr t2) 8 := by
    rw [hsp2]
    exact (hRead 40 (by decide)).of_external_eq hm2
  have hc3 : CodeIn (codeRange 0x1137a8 (encodePopR64 12)) t2 :=
    programText_slice (code.of_external_eq hm2) 0x137a8 _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨t3, ha3, hr3, he3⟩ :=
    (P256.Proofs.Program.pop_register_effect_step 0x1137a8 12 (by decide)).advances hr2 hc3
      ⟨he2.rip, hread2⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x137aa (by decide)))
  change (popR64Effect 0x1137a8 2 12 t2).Holds t2 t3 at he3
  have hm3 : t3.external = t.external :=
    (he3.agrees.external (by simp [Component.Covers])).trans hm2
  have hsp3 : stackPtr t3 = stackPtr s - 32 := by
    have hw : stackPtr t3 = stackPtr t2 + 8 := he3.writes.2
    rw [hw, hsp2]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have hv3 : (Operand.reg 12 : Operand 64).read t3 = s.regValue .r12 := by
    have hw : (Operand.reg 12 : Operand 64).read t3 =
        (Operand.mem (stackPtr t2) : Operand 64).read t2 := he3.writes.1
    rw [hw, hsp2]
    change memLoad t2.external (stackPtr s - 40) 64 = _
    rw [hm2]
    exact state.saved (.r12, 40) (by simp [P256.Proofs.Program.savedRegisters])
  have hread3 : MemReadable t3 (stackPtr t3) 8 := by
    rw [hsp3]
    exact (hRead 32 (by decide)).of_external_eq hm3
  have hc4 : CodeIn (codeRange 0x1137aa (encodePopR64 13)) t3 :=
    programText_slice (code.of_external_eq hm3) 0x137aa _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨t4, ha4, hr4, he4⟩ :=
    (P256.Proofs.Program.pop_register_effect_step 0x1137aa 13 (by decide)).advances hr3 hc4
      ⟨he3.rip, hread3⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x137ac (by decide)))
  change (popR64Effect 0x1137aa 2 13 t3).Holds t3 t4 at he4
  have hm4 : t4.external = t.external :=
    (he4.agrees.external (by simp [Component.Covers])).trans hm3
  have hsp4 : stackPtr t4 = stackPtr s - 24 := by
    have hw : stackPtr t4 = stackPtr t3 + 8 := he4.writes.2
    rw [hw, hsp3]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have hv4 : (Operand.reg 13 : Operand 64).read t4 = s.regValue .r13 := by
    have hw : (Operand.reg 13 : Operand 64).read t4 =
        (Operand.mem (stackPtr t3) : Operand 64).read t3 := he4.writes.1
    rw [hw, hsp3]
    change memLoad t3.external (stackPtr s - 32) 64 = _
    rw [hm3]
    exact state.saved (.r13, 32) (by simp [P256.Proofs.Program.savedRegisters])
  have hread4 : MemReadable t4 (stackPtr t4) 8 := by
    rw [hsp4]
    exact (hRead 24 (by decide)).of_external_eq hm4
  have hc5 : CodeIn (codeRange 0x1137ac (encodePopR64 14)) t4 :=
    programText_slice (code.of_external_eq hm4) 0x137ac _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨t5, ha5, hr5, he5⟩ :=
    (P256.Proofs.Program.pop_register_effect_step 0x1137ac 14 (by decide)).advances hr4 hc5
      ⟨he4.rip, hread4⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x137ae (by decide)))
  change (popR64Effect 0x1137ac 2 14 t4).Holds t4 t5 at he5
  have hm5 : t5.external = t.external :=
    (he5.agrees.external (by simp [Component.Covers])).trans hm4
  have hsp5 : stackPtr t5 = stackPtr s - 16 := by
    have hw : stackPtr t5 = stackPtr t4 + 8 := he5.writes.2
    rw [hw, hsp4]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have hv5 : (Operand.reg 14 : Operand 64).read t5 = s.regValue .r14 := by
    have hw : (Operand.reg 14 : Operand 64).read t5 =
        (Operand.mem (stackPtr t4) : Operand 64).read t4 := he5.writes.1
    rw [hw, hsp4]
    change memLoad t4.external (stackPtr s - 24) 64 = _
    rw [hm4]
    exact state.saved (.r14, 24) (by simp [P256.Proofs.Program.savedRegisters])
  have hread5 : MemReadable t5 (stackPtr t5) 8 := by
    rw [hsp5]
    exact (hRead 16 (by decide)).of_external_eq hm5
  have hc6 : CodeIn (codeRange 0x1137ae (encodePopR64 15)) t5 :=
    programText_slice (code.of_external_eq hm5) 0x137ae _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨t6, ha6, hr6, he6⟩ :=
    (P256.Proofs.Program.pop_register_effect_step 0x1137ae 15 (by decide)).advances hr5 hc6
      ⟨he5.rip, hread5⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x137b0 (by decide)))
  change (popR64Effect 0x1137ae 2 15 t5).Holds t5 t6 at he6
  have hm6 : t6.external = t.external :=
    (he6.agrees.external (by simp [Component.Covers])).trans hm5
  have hsp6 : stackPtr t6 = stackPtr s - 8 := by
    have hw : stackPtr t6 = stackPtr t5 + 8 := he6.writes.2
    rw [hw, hsp5]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have hv6 : (Operand.reg 15 : Operand 64).read t6 = s.regValue .r15 := by
    have hw : (Operand.reg 15 : Operand 64).read t6 =
        (Operand.mem (stackPtr t5) : Operand 64).read t5 := he6.writes.1
    rw [hw, hsp5]
    change memLoad t5.external (stackPtr s - 16) 64 = _
    rw [hm5]
    exact state.saved (.r15, 16) (by simp [P256.Proofs.Program.savedRegisters])
  have hread6 : MemReadable t6 (stackPtr t6) 8 := by
    rw [hsp6]
    exact (hRead 8 (by decide)).of_external_eq hm6
  have hc7 : CodeIn (codeRange 0x1137b0 (encodePopR64 5)) t6 :=
    programText_slice (code.of_external_eq hm6) 0x137b0 _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨t7, ha7, hr7, he7⟩ :=
    (P256.Proofs.Program.pop_register_effect_step 0x1137b0 5 (by decide)).advances hr6 hc7
      ⟨he6.rip, hread6⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x137b1 (by decide)))
  change (popR64Effect 0x1137b0 1 5 t6).Holds t6 t7 at he7
  have hm7 : t7.external = t.external :=
    (he7.agrees.external (by simp [Component.Covers])).trans hm6
  have hsp7 : stackPtr t7 = stackPtr s - 0 := by
    have hw : stackPtr t7 = stackPtr t6 + 8 := he7.writes.2
    rw [hw, hsp6]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have hv7 : (Operand.reg 5 : Operand 64).read t7 = s.regValue .rbp := by
    have hw : (Operand.reg 5 : Operand 64).read t7 =
        (Operand.mem (stackPtr t6) : Operand 64).read t6 := he7.writes.1
    rw [hw, hsp6]
    change memLoad t6.external (stackPtr s - 8) 64 = _
    rw [hm6]
    exact state.saved (.rbp, 8) (by simp [P256.Proofs.Program.savedRegisters])
  have hsp7' : stackPtr t7 = stackPtr s := by simpa using hsp7
  have hread7 : MemReadable t7 (stackPtr t7) 8 := by
    rw [hsp7']
    simpa using (hRead 0 (by decide)).of_external_eq hm7
  have htop7 : stackTop t7 = (returnBoundary s).rip := by
    rw [stackTop, hsp7']
    change memLoad t7.external (stackPtr s) 64 = _
    rw [hm7]
    exact state.returnAddress
  have hc8 : CodeIn (codeRange 0x1137b1 [0xc3]) t7 :=
    programText_slice (code.of_external_eq hm7) 0x137b1 _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨u, ha8, hr8, he8⟩ := (ret_effect_step 0x1137b1).advances hr7 hc8
    ⟨⟨he7.rip, hread7⟩, htop7 ▸ inProgram_low pre.returnInProgram⟩
    (by change stackTop t7 ≠ boundary.rip
        rw [htop7]
        exact boundary_ne_program pre.outerBoundary pre.returnInProgram)
  have hm8 : u.external = t.external :=
    (he8.agrees.external (by simp [Component.Covers])).trans hm7
  have hf := (((((((he1.agrees.trans he2.agrees).trans he3.agrees).trans he4.agrees).trans he5.agrees).trans he6.agrees).trans he7.agrees).trans he8.agrees)
  obtain ⟨fuel, hexec⟩ := execution
  refine ⟨u, ?_, hm8⟩
  refine ⟨⟨fuel + 8, ?_⟩, he8.rip.trans htop7, ?_,
    bindingsSupported_of_ready_agrees state.bindingsSupported hr8 hf,
    supportedMachine_of_ready_agrees state.machine hr8 hf, ?_,
    hf.directionFlagClear (by simp) state.directionFlag,
    (hf.mxcsr (by simp)).trans state.mxcsr,
    (hf.fcw (by simp)).trans state.fp87, ?_, ?_, ?_⟩
  · exact ((((((((hexec.trans ha1).trans ha2).trans ha3).trans ha4).trans ha5).trans ha6).trans ha7).trans ha8)
  · change stackPtr u = stackPtr s + 8
    have hw : stackPtr u = stackPtr t7 + 8 := he8.writes
    rw [hw, hsp7']
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (Operand.reg 3 : Operand 64).read u = _
      rw [he8.agrees.read (by simp), he7.agrees.read (by simp), he6.agrees.read (by simp), he5.agrees.read (by simp), he4.agrees.read (by simp), he3.agrees.read (by simp)]
      exact hv2
    · change (Operand.reg 5 : Operand 64).read u = _
      rw [he8.agrees.read (by simp)]
      exact hv7
    · change (Operand.reg 12 : Operand 64).read u = _
      rw [he8.agrees.read (by simp), he7.agrees.read (by simp), he6.agrees.read (by simp), he5.agrees.read (by simp), he4.agrees.read (by simp)]
      exact hv3
    · change (Operand.reg 13 : Operand 64).read u = _
      rw [he8.agrees.read (by simp), he7.agrees.read (by simp), he6.agrees.read (by simp), he5.agrees.read (by simp)]
      exact hv4
    · change (Operand.reg 14 : Operand 64).read u = _
      rw [he8.agrees.read (by simp), he7.agrees.read (by simp), he6.agrees.read (by simp)]
      exact hv5
    · change (Operand.reg 15 : Operand 64).read u = _
      rw [he8.agrees.read (by simp), he7.agrees.read (by simp)]
      exact hv6
  · intro address hout
    rw [hm8]
    exact state.frame address hout
  · intro address byte hfetch
    rw [hm8]
    exact state.loaded address byte hfetch
  · intro address ha
    rw [hm8]
    exact state.allocated address ha

end P256.Proofs.Sec1.SquareRoot.Square.Reduction
