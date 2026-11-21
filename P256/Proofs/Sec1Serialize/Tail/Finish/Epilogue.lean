import P256.Proofs.Sec1Serialize.State
import P256.Proofs.Program.Pop
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import X86Proofs.Instructions.Call.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1Serialize

open P256.Spec P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

theorem serialization_epilogue [bindings : Bindings] {s t : RamState}
    {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x110d70 72 65 328)
    (stage : FrameState s t 65 328 312)
    (execution : ∃ n, Advances boundary n s t)
    (rip : t.RIP = 0x1111e1)
    (destination : t.regValue .rbp = s.regValue .rdi) :
    ∃ u, CalleeResult s u boundary 65 328 ∧ u.regValue .rax = s.regValue .rdi ∧
      u.external = t.external := by
  have code := programLoaded_codeIn stage.loaded
  have hRead (offset : Nat) (ho : offset ≤ 328) :
      MemReadable t (stackPtr s - BitVec.ofNat 64 offset) 8 :=
    readable_of_grow (stack_sub_readable pre.stack ho (by omega)) stage.allocated
  have hc1 : CodeIn (codeRange 0x1111e1 [0x48, 0x89, 0xe8]) t :=
    programText_slice code 0x111e1 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t1, ha1, hr1, he1⟩ :=
    (mov_r64_r64_effect_step 0x1111e1 0x48 0xe8
      (by simp [RexWPrefix]) (by decide)).advances
      (readyToStep stage.machine stage.bindingsSupported) hc1 rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x111e4 (by decide)))
  change (movR64R64Effect 0x1111e1 0 5 t).Holds t t1 at he1
  have hm1 : t1.external = t.external := he1.agrees.external (by simp [Component.Covers])
  have hsp1 : stackPtr t1 = stackPtr s - 312 :=
    (he1.agrees.read (n := 64) (r := 4) (by simp)).trans stage.rsp
  have hc2 : CodeIn (codeRange 0x1111e4 [0x48, 0x81, 0xc4, 8, 1, 0, 0]) t1 :=
    programText_slice (code.of_external_eq hm1) 0x111e4 _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨t2, ha2, hr2, he2⟩ :=
    (add_r64_imm32_effect_step 0x1111e4 0x48 0xc4 264
      (by simp [RexWPrefix]) (by decide) (by decide)).advances hr1 hc2 he1.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x111eb (by decide)))
  change (addR64Imm32Effect 0x1111e4 4 264 t1).Holds t1 t2 at he2
  have hm2 : t2.external = t.external :=
    (he2.agrees.external (by simp [Component.Covers])).trans hm1
  have hsp2 : stackPtr t2 = stackPtr s - 48 := by
    have hw : stackPtr t2 = stackPtr t1 + 264 := he2.writes
    rw [hw, hsp1]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have hread2 : MemReadable t2 (stackPtr t2) 8 := by
    rw [hsp2]
    exact (hRead 48 (by decide)).of_external_eq hm2
  have hc3 : CodeIn (codeRange 0x1111eb (encodePopR64 3)) t2 :=
    programText_slice (code.of_external_eq hm2) 0x111eb _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨t3, ha3, hr3, he3⟩ :=
    (pop_register_effect_step 0x1111eb 3 (by decide)).advances hr2 hc3
      ⟨he2.rip, hread2⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x111ec (by decide)))
  change (popR64Effect 0x1111eb 1 3 t2).Holds t2 t3 at he3
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
    exact stage.saved (.rbx, 48) (by simp [savedRegisters])
  have hread3 : MemReadable t3 (stackPtr t3) 8 := by
    rw [hsp3]
    exact (hRead 40 (by decide)).of_external_eq hm3
  have hc4 : CodeIn (codeRange 0x1111ec (encodePopR64 12)) t3 :=
    programText_slice (code.of_external_eq hm3) 0x111ec _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨t4, ha4, hr4, he4⟩ :=
    (pop_register_effect_step 0x1111ec 12 (by decide)).advances hr3 hc4
      ⟨he3.rip, hread3⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x111ee (by decide)))
  change (popR64Effect 0x1111ec 2 12 t3).Holds t3 t4 at he4
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
    exact stage.saved (.r12, 40) (by simp [savedRegisters])
  have hread4 : MemReadable t4 (stackPtr t4) 8 := by
    rw [hsp4]
    exact (hRead 32 (by decide)).of_external_eq hm4
  have hc5 : CodeIn (codeRange 0x1111ee (encodePopR64 13)) t4 :=
    programText_slice (code.of_external_eq hm4) 0x111ee _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨t5, ha5, hr5, he5⟩ :=
    (pop_register_effect_step 0x1111ee 13 (by decide)).advances hr4 hc5
      ⟨he4.rip, hread4⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x111f0 (by decide)))
  change (popR64Effect 0x1111ee 2 13 t4).Holds t4 t5 at he5
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
    exact stage.saved (.r13, 32) (by simp [savedRegisters])
  have hread5 : MemReadable t5 (stackPtr t5) 8 := by
    rw [hsp5]
    exact (hRead 24 (by decide)).of_external_eq hm5
  have hc6 : CodeIn (codeRange 0x1111f0 (encodePopR64 14)) t5 :=
    programText_slice (code.of_external_eq hm5) 0x111f0 _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨t6, ha6, hr6, he6⟩ :=
    (pop_register_effect_step 0x1111f0 14 (by decide)).advances hr5 hc6
      ⟨he5.rip, hread5⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x111f2 (by decide)))
  change (popR64Effect 0x1111f0 2 14 t5).Holds t5 t6 at he6
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
    exact stage.saved (.r14, 24) (by simp [savedRegisters])
  have hread6 : MemReadable t6 (stackPtr t6) 8 := by
    rw [hsp6]
    exact (hRead 16 (by decide)).of_external_eq hm6
  have hc7 : CodeIn (codeRange 0x1111f2 (encodePopR64 15)) t6 :=
    programText_slice (code.of_external_eq hm6) 0x111f2 _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨t7, ha7, hr7, he7⟩ :=
    (pop_register_effect_step 0x1111f2 15 (by decide)).advances hr6 hc7
      ⟨he6.rip, hread6⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x111f4 (by decide)))
  change (popR64Effect 0x1111f2 2 15 t6).Holds t6 t7 at he7
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
    exact stage.saved (.r15, 16) (by simp [savedRegisters])
  have hread7 : MemReadable t7 (stackPtr t7) 8 := by
    rw [hsp7]
    exact (hRead 8 (by decide)).of_external_eq hm7
  have hc8 : CodeIn (codeRange 0x1111f4 (encodePopR64 5)) t7 :=
    programText_slice (code.of_external_eq hm7) 0x111f4 _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨t8, ha8, hr8, he8⟩ :=
    (pop_register_effect_step 0x1111f4 5 (by decide)).advances hr7 hc8
      ⟨he7.rip, hread7⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x111f5 (by decide)))
  change (popR64Effect 0x1111f4 1 5 t7).Holds t7 t8 at he8
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
    exact stage.saved (.rbp, 8) (by simp [savedRegisters])
  have hsp8' : stackPtr t8 = stackPtr s := by simpa using hsp8
  have hread8 : MemReadable t8 (stackPtr t8) 8 := by
    rw [hsp8']
    simpa using (hRead 0 (by decide)).of_external_eq hm8
  have htop8 : stackTop t8 = (returnBoundary s).rip := by
    rw [stackTop, hsp8']
    change memLoad t8.external (stackPtr s) 64 = _
    rw [hm8]
    exact stage.returnAddress
  have hc9 : CodeIn (codeRange 0x1111f5 [0xc3]) t8 :=
    programText_slice (code.of_external_eq hm8) 0x111f5 _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨u, ha9, hr9, he9⟩ := (ret_effect_step 0x1111f5).advances hr8 hc9
    ⟨⟨he8.rip, hread8⟩, htop8 ▸ inProgram_low pre.returnInProgram⟩
    (by change stackTop t8 ≠ boundary.rip
        rw [htop8]
        exact boundary_ne_program pre.outerBoundary pre.returnInProgram)
  have hm9 : u.external = t.external :=
    (he9.agrees.external (by simp [Component.Covers])).trans hm8
  have hf := ((((((((he1.agrees.trans he2.agrees).trans he3.agrees).trans
    he4.agrees).trans he5.agrees).trans he6.agrees).trans he7.agrees).trans
    he8.agrees).trans he9.agrees)
  obtain ⟨fuel, hexec⟩ := execution
  refine ⟨u, {
    execution := ⟨fuel + 9, ?_⟩
    rip := he9.rip.trans htop8
    rsp := ?_
    bindingsSupported := bindingsSupported_of_ready_agrees stage.bindingsSupported hr9 hf
    machine := supportedMachine_of_ready_agrees stage.machine hr9 hf
    calleeSaved := ?_
    directionFlag := hf.directionFlagClear (by simp) stage.directionFlag
    mxcsr := (hf.mxcsr (by simp)).trans stage.mxcsr
    fp87 := (hf.fcw (by simp)).trans stage.fp87
    frame := ?_
    loaded := ?_
    allocated := fun a ha => hf.grow a (stage.allocated a ha)
  }, ?_, hm9⟩
  · exact (((((((((hexec.trans ha1).trans ha2).trans ha3).trans ha4).trans ha5).trans
      ha6).trans ha7).trans ha8).trans ha9)
  · change stackPtr u = stackPtr s + 8
    have hw : stackPtr u = stackPtr t8 + 8 := he9.writes
    rw [hw, hsp8']
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (Operand.reg 3 : Operand 64).read u = _
      rw [he9.agrees.read (by simp), he8.agrees.read (by simp), he7.agrees.read (by simp),
        he6.agrees.read (by simp), he5.agrees.read (by simp), he4.agrees.read (by simp)]
      exact hv3
    · change (Operand.reg 5 : Operand 64).read u = _
      rw [he9.agrees.read (by simp)]
      exact hv8
    · change (Operand.reg 12 : Operand 64).read u = _
      rw [he9.agrees.read (by simp), he8.agrees.read (by simp), he7.agrees.read (by simp),
        he6.agrees.read (by simp), he5.agrees.read (by simp)]
      exact hv4
    · change (Operand.reg 13 : Operand 64).read u = _
      rw [he9.agrees.read (by simp), he8.agrees.read (by simp), he7.agrees.read (by simp),
        he6.agrees.read (by simp)]
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
  · change (Operand.reg 0 : Operand 64).read u = _
    rw [he9.agrees.read (by simp), he8.agrees.read (by simp), he7.agrees.read (by simp),
      he6.agrees.read (by simp), he5.agrees.read (by simp), he4.agrees.read (by simp),
      he3.agrees.read (by simp), he2.agrees.read (by simp)]
    exact he1.writes.trans destination

end P256.Proofs.Sec1Serialize
