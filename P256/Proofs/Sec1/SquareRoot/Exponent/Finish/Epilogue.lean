import P256.Proofs.Sec1.SquareRoot.Exponent.State
import P256.Proofs.Program.Pop
import P256.Proofs.Program.Stack
import P256.Proofs.Program.Code
import P256.Proofs.Program.State
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import X86Proofs.Instructions.Call.Triple

set_option autoImplicit false

open P256.Proofs.Program

namespace P256.Proofs.Sec1.SquareRoot

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem exponent_epilogue [bindings : Bindings] {s t : RamState}
    {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x114ba0 144 32 1584)
    (stage : ExponentFrame s t)
    (execution : ∃ fuel, Advances boundary fuel s t)
    (rip : t.RIP = 0x11594e) :
    ∃ u, CalleeResult s u boundary 32 1584 ∧ u.external = t.external := by
  have code := programLoaded_codeIn stage.loaded
  have hRead (offset : Nat) (ho : offset ≤ 1584) :
      MemReadable t (stackPtr s - BitVec.ofNat 64 offset) 8 :=
    readable_of_grow (stack_sub_readable pre.stack ho (by omega)) stage.allocated
  have hr1 : ReadyToStep t := readyToStep stage.machine stage.bindingsSupported
  have hm1 : t.external = t.external := rfl
  have hsp1 : stackPtr t = stackPtr s - 1416 := stage.rsp
  have hc2 : CodeIn (codeRange 0x11594e [0x48, 0x81, 0xc4, 0x58, 5, 0, 0]) t :=
    programText_slice (code.of_external_eq hm1) 0x1594e _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨t2, ha2, hr2, he2⟩ :=
    (add_r64_imm32_effect_step 0x11594e 0x48 0xc4 1368
      (by simp [RexWPrefix]) (by decide) (by decide)).advances hr1 hc2 rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x15955 (by decide)))
  change (addR64Imm32Effect 0x11594e 4 1368 t).Holds t t2 at he2
  have hm2 : t2.external = t.external :=
    (he2.agrees.external (by simp [Component.Covers])).trans hm1
  have hsp2 : stackPtr t2 = stackPtr s - 48 := by
    have hw : stackPtr t2 = stackPtr t + 1368 := he2.writes
    rw [hw, hsp1]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have hread2 : MemReadable t2 (stackPtr t2) 8 := by
    rw [hsp2]
    exact (hRead 48 (by decide)).of_external_eq hm2
  have hc3 : CodeIn (codeRange 0x115955 (encodePopR64 3)) t2 :=
    programText_slice (code.of_external_eq hm2) 0x15955 _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨t3, ha3, hr3, he3⟩ :=
    (pop_register_effect_step 0x115955 3 (by decide)).advances hr2 hc3
      ⟨he2.rip, hread2⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x15956 (by decide)))
  change (popR64Effect 0x115955 1 3 t2).Holds t2 t3 at he3
  have hm3 : t3.external = t.external :=
    (he3.agrees.external (by simp [Component.Covers])).trans hm2
  have hsp3 : stackPtr t3 = stackPtr s - 40 := by
    have hw : stackPtr t3 = stackPtr t2 + 8 := he3.writes.2
    rw [hw, hsp2]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have hv3 : (Operand.reg 3 : Operand 64).read t3 = s.regValue .rbx := by
    have hw : (Operand.reg 3 : Operand 64).read t3 =
        (Operand.mem (stackPtr t2) : Operand 64).read t2 := he3.writes.1
    rw [hw, hsp2]
    change memLoad t2.external (stackPtr s - 48) 64 = _
    rw [hm2]
    exact stage.saved 5 (by decide)
  have hread3 : MemReadable t3 (stackPtr t3) 8 := by
    rw [hsp3]
    exact (hRead 40 (by decide)).of_external_eq hm3
  have hc4 : CodeIn (codeRange 0x115956 (encodePopR64 12)) t3 :=
    programText_slice (code.of_external_eq hm3) 0x15956 _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨t4, ha4, hr4, he4⟩ :=
    (pop_register_effect_step 0x115956 12 (by decide)).advances hr3 hc4
      ⟨he3.rip, hread3⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x15958 (by decide)))
  change (popR64Effect 0x115956 2 12 t3).Holds t3 t4 at he4
  have hm4 : t4.external = t.external :=
    (he4.agrees.external (by simp [Component.Covers])).trans hm3
  have hsp4 : stackPtr t4 = stackPtr s - 32 := by
    have hw : stackPtr t4 = stackPtr t3 + 8 := he4.writes.2
    rw [hw, hsp3]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have hv4 : (Operand.reg 12 : Operand 64).read t4 = s.regValue .r12 := by
    have hw : (Operand.reg 12 : Operand 64).read t4 =
        (Operand.mem (stackPtr t3) : Operand 64).read t3 := he4.writes.1
    rw [hw, hsp3]
    change memLoad t3.external (stackPtr s - 40) 64 = _
    rw [hm3]
    exact stage.saved 4 (by decide)
  have hread4 : MemReadable t4 (stackPtr t4) 8 := by
    rw [hsp4]
    exact (hRead 32 (by decide)).of_external_eq hm4
  have hc5 : CodeIn (codeRange 0x115958 (encodePopR64 13)) t4 :=
    programText_slice (code.of_external_eq hm4) 0x15958 _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨t5, ha5, hr5, he5⟩ :=
    (pop_register_effect_step 0x115958 13 (by decide)).advances hr4 hc5
      ⟨he4.rip, hread4⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1595a (by decide)))
  change (popR64Effect 0x115958 2 13 t4).Holds t4 t5 at he5
  have hm5 : t5.external = t.external :=
    (he5.agrees.external (by simp [Component.Covers])).trans hm4
  have hsp5 : stackPtr t5 = stackPtr s - 24 := by
    have hw : stackPtr t5 = stackPtr t4 + 8 := he5.writes.2
    rw [hw, hsp4]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have hv5 : (Operand.reg 13 : Operand 64).read t5 = s.regValue .r13 := by
    have hw : (Operand.reg 13 : Operand 64).read t5 =
        (Operand.mem (stackPtr t4) : Operand 64).read t4 := he5.writes.1
    rw [hw, hsp4]
    change memLoad t4.external (stackPtr s - 32) 64 = _
    rw [hm4]
    exact stage.saved 3 (by decide)
  have hread5 : MemReadable t5 (stackPtr t5) 8 := by
    rw [hsp5]
    exact (hRead 24 (by decide)).of_external_eq hm5
  have hc6 : CodeIn (codeRange 0x11595a (encodePopR64 14)) t5 :=
    programText_slice (code.of_external_eq hm5) 0x1595a _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨t6, ha6, hr6, he6⟩ :=
    (pop_register_effect_step 0x11595a 14 (by decide)).advances hr5 hc6
      ⟨he5.rip, hread5⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1595c (by decide)))
  change (popR64Effect 0x11595a 2 14 t5).Holds t5 t6 at he6
  have hm6 : t6.external = t.external :=
    (he6.agrees.external (by simp [Component.Covers])).trans hm5
  have hsp6 : stackPtr t6 = stackPtr s - 16 := by
    have hw : stackPtr t6 = stackPtr t5 + 8 := he6.writes.2
    rw [hw, hsp5]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have hv6 : (Operand.reg 14 : Operand 64).read t6 = s.regValue .r14 := by
    have hw : (Operand.reg 14 : Operand 64).read t6 =
        (Operand.mem (stackPtr t5) : Operand 64).read t5 := he6.writes.1
    rw [hw, hsp5]
    change memLoad t5.external (stackPtr s - 24) 64 = _
    rw [hm5]
    exact stage.saved 2 (by decide)
  have hread6 : MemReadable t6 (stackPtr t6) 8 := by
    rw [hsp6]
    exact (hRead 16 (by decide)).of_external_eq hm6
  have hc7 : CodeIn (codeRange 0x11595c (encodePopR64 15)) t6 :=
    programText_slice (code.of_external_eq hm6) 0x1595c _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨t7, ha7, hr7, he7⟩ :=
    (pop_register_effect_step 0x11595c 15 (by decide)).advances hr6 hc7
      ⟨he6.rip, hread6⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1595e (by decide)))
  change (popR64Effect 0x11595c 2 15 t6).Holds t6 t7 at he7
  have hm7 : t7.external = t.external :=
    (he7.agrees.external (by simp [Component.Covers])).trans hm6
  have hsp7 : stackPtr t7 = stackPtr s - 8 := by
    have hw : stackPtr t7 = stackPtr t6 + 8 := he7.writes.2
    rw [hw, hsp6]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have hv7 : (Operand.reg 15 : Operand 64).read t7 = s.regValue .r15 := by
    have hw : (Operand.reg 15 : Operand 64).read t7 =
        (Operand.mem (stackPtr t6) : Operand 64).read t6 := he7.writes.1
    rw [hw, hsp6]
    change memLoad t6.external (stackPtr s - 16) 64 = _
    rw [hm6]
    exact stage.saved 1 (by decide)
  have hread7 : MemReadable t7 (stackPtr t7) 8 := by
    rw [hsp7]
    exact (hRead 8 (by decide)).of_external_eq hm7
  have hc8 : CodeIn (codeRange 0x11595e (encodePopR64 5)) t7 :=
    programText_slice (code.of_external_eq hm7) 0x1595e _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨t8, ha8, hr8, he8⟩ :=
    (pop_register_effect_step 0x11595e 5 (by decide)).advances hr7 hc8
      ⟨he7.rip, hread7⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1595f (by decide)))
  change (popR64Effect 0x11595e 1 5 t7).Holds t7 t8 at he8
  have hm8 : t8.external = t.external :=
    (he8.agrees.external (by simp [Component.Covers])).trans hm7
  have hsp8 : stackPtr t8 = stackPtr s - 0 := by
    have hw : stackPtr t8 = stackPtr t7 + 8 := he8.writes.2
    rw [hw, hsp7]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have hv8 : (Operand.reg 5 : Operand 64).read t8 = s.regValue .rbp := by
    have hw : (Operand.reg 5 : Operand 64).read t8 =
        (Operand.mem (stackPtr t7) : Operand 64).read t7 := he8.writes.1
    rw [hw, hsp7]
    change memLoad t7.external (stackPtr s - 8) 64 = _
    rw [hm7]
    exact stage.saved 0 (by decide)
  have hsp8' : stackPtr t8 = stackPtr s := by simpa using hsp8
  have hread8 : MemReadable t8 (stackPtr t8) 8 := by
    rw [hsp8']
    simpa using (hRead 0 (by decide)).of_external_eq hm8
  have htop8 : stackTop t8 = (returnBoundary s).rip := by
    rw [stackTop, hsp8']
    change memLoad t8.external (stackPtr s) 64 = _
    rw [hm8]
    exact stage.returnAddress
  have hc9 : CodeIn (codeRange 0x11595f [0xc3]) t8 :=
    programText_slice (code.of_external_eq hm8) 0x1595f _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨u, ha9, hr9, he9⟩ := (ret_effect_step 0x11595f).advances hr8 hc9
    ⟨⟨he8.rip, hread8⟩, htop8 ▸ inProgram_low pre.returnInProgram⟩
    (by change stackTop t8 ≠ boundary.rip
        rw [htop8]
        exact boundary_ne_program pre.outerBoundary pre.returnInProgram)
  have hm9 : u.external = t.external :=
    (he9.agrees.external (by simp [Component.Covers])).trans hm8
  have hf := ((((((he2.agrees.trans he3.agrees).trans he4.agrees).trans he5.agrees).trans he6.agrees).trans he7.agrees).trans he8.agrees).trans he9.agrees
  obtain ⟨fuel, hexec⟩ := execution
  refine ⟨u, ?_, hm9⟩
  refine ⟨⟨fuel + 8, ?_⟩, he9.rip.trans htop8, ?_,
    bindingsSupported_of_ready_agrees stage.bindingsSupported hr9 hf,
    supportedMachine_of_ready_agrees stage.machine hr9 hf, ?_,
    hf.directionFlagClear (by simp) stage.directionFlag,
    (hf.mxcsr (by simp)).trans stage.mxcsr,
    (hf.fcw (by simp)).trans stage.fp87,
    ?_, ?_, (fun a ha => hf.grow a (stage.allocated a ha))⟩
  · exact ((((((((hexec.trans ha2).trans ha3).trans ha4).trans ha5).trans ha6).trans ha7).trans ha8).trans ha9)
  · change stackPtr u = stackPtr s + 8
    have hw : stackPtr u = stackPtr t8 + 8 := he9.writes
    rw [hw, hsp8']
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (Operand.reg 3 : Operand 64).read u = _
      rw [he9.agrees.read (by simp), he8.agrees.read (by simp), he7.agrees.read (by simp), he6.agrees.read (by simp), he5.agrees.read (by simp), he4.agrees.read (by simp)]
      exact hv3
    · change (Operand.reg 5 : Operand 64).read u = _
      rw [he9.agrees.read (by simp)]
      exact hv8
    · change (Operand.reg 12 : Operand 64).read u = _
      rw [he9.agrees.read (by simp), he8.agrees.read (by simp), he7.agrees.read (by simp), he6.agrees.read (by simp), he5.agrees.read (by simp)]
      exact hv4
    · change (Operand.reg 13 : Operand 64).read u = _
      rw [he9.agrees.read (by simp), he8.agrees.read (by simp), he7.agrees.read (by simp), he6.agrees.read (by simp)]
      exact hv5
    · change (Operand.reg 14 : Operand 64).read u = _
      rw [he9.agrees.read (by simp), he8.agrees.read (by simp), he7.agrees.read (by simp)]
      exact hv6
    · change (Operand.reg 15 : Operand 64).read u = _
      rw [he9.agrees.read (by simp), he8.agrees.read (by simp)]
      exact hv7
  · intro address hout
    rw [hm9]
    exact stage.frame address hout
  · intro address byte hfetch
    rw [hm9]
    exact stage.loaded address byte hfetch

end P256.Proofs.Sec1.SquareRoot
