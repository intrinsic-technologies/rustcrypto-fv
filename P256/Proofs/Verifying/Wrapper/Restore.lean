import P256.Proofs.Verifying.Wrapper.ReturnState
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import P256.Proofs.Program.Pop
import X86Proofs.Instructions.Call.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem restore [bindings : Bindings] {s t : RamState}
    (state : ReturnState s t) (stack : Stack.Valid s 10280)
    (outside : ¬ InProgram (returnBoundary s).rip)
    (low : (returnBoundary s).rip.toNat < 2^32) (rip : t.RIP = 0x103220) :
    ∃ u, Returns (returnBoundary s) 7 t u ∧
      SupportedIntegerMachineState bindings.processor u ∧
      MachineRamUnitStrideDecodable bindings u ∧
      CalleeSavedRegistersUnchanged s u ∧ DirectionFlagUnset u ∧
      u.external = t.external ∧ u.regValue .rax = t.regValue .rax := by
  have code := programLoaded_codeIn state.loaded
  have hRead (offset : Nat) (ho : offset ≤ 10280) :
      MemReadable t (stackPtr s - BitVec.ofNat 64 offset) 8 :=
    readable_of_grow (stack_sub_readable stack ho (by omega)) state.allocated
  have hc1 : CodeIn (codeRange 0x103220 [72, 129, 196, 240, 0, 0, 0]) t :=
    programText_slice code 0x3220 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t1, ha1, hr1, he1⟩ :=
    (add_r64_imm32_effect_step 0x103220 0x48 0xc4 240
      (by simp [RexWPrefix]) (by decide) (by decide)).advances
      (readyToStep state.machine state.bindingsSupported) hc1 rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x3227 (by decide)))
  change (addR64Imm32Effect 0x103220 4 240 t).Holds t t1 at he1
  have hm1 : t1.external = t.external := he1.agrees.external (by simp [Component.Covers])
  have hsp1 : stackPtr t1 = stackPtr s - 40 := by
    have hw : stackPtr t1 = stackPtr t + 240 := he1.writes
    rw [hw, state.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have hread1 : MemReadable t1 (stackPtr t1) 8 := by
    rw [hsp1]
    exact (hRead 40 (by decide)).of_external_eq hm1
  have hc2 : CodeIn (codeRange 0x103227 (encodePopR64 3)) t1 :=
    programText_slice (code.of_external_eq hm1) 0x3227 _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨t2, ha2, hr2, he2⟩ :=
    (pop_register_effect_step 0x103227 3 (by decide)).advances hr1 hc2
      ⟨he1.rip, hread1⟩
      (boundary_ne_program outside (inProgram_of_textOffset 0x3228 (by decide)))
  change (popR64Effect 0x103227 1 3 t1).Holds t1 t2 at he2
  have hm2 : t2.external = t.external :=
    (he2.agrees.external (by simp [Component.Covers])).trans hm1
  have hsp2 : stackPtr t2 = stackPtr s - 32 := by
    have hw : stackPtr t2 = stackPtr t1 + 8 := he2.writes.2
    rw [hw, hsp1]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have hv2 : (Operand.reg 3 : Operand 64).read t2 = s.regValue .rbx := by
    have hw : (Operand.reg 3 : Operand 64).read t2 =
        (Operand.mem (stackPtr t1) : Operand 64).read t1 := he2.writes.1
    rw [hw, hsp1]
    change memLoad t1.external (stackPtr s - 40) 64 = _
    rw [hm1]
    exact state.saved (.rbx, 40) (by simp [savedRegisters])
  have hread2 : MemReadable t2 (stackPtr t2) 8 := by
    rw [hsp2]
    exact (hRead 32 (by decide)).of_external_eq hm2
  have hc3 : CodeIn (codeRange 0x103228 (encodePopR64 12)) t2 :=
    programText_slice (code.of_external_eq hm2) 0x3228 _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨t3, ha3, hr3, he3⟩ :=
    (pop_register_effect_step 0x103228 12 (by decide)).advances hr2 hc3
      ⟨he2.rip, hread2⟩
      (boundary_ne_program outside (inProgram_of_textOffset 0x322a (by decide)))
  change (popR64Effect 0x103228 2 12 t2).Holds t2 t3 at he3
  have hm3 : t3.external = t.external :=
    (he3.agrees.external (by simp [Component.Covers])).trans hm2
  have hsp3 : stackPtr t3 = stackPtr s - 24 := by
    have hw : stackPtr t3 = stackPtr t2 + 8 := he3.writes.2
    rw [hw, hsp2]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have hv3 : (Operand.reg 12 : Operand 64).read t3 = s.regValue .r12 := by
    have hw : (Operand.reg 12 : Operand 64).read t3 =
        (Operand.mem (stackPtr t2) : Operand 64).read t2 := he3.writes.1
    rw [hw, hsp2]
    change memLoad t2.external (stackPtr s - 32) 64 = _
    rw [hm2]
    exact state.saved (.r12, 32) (by simp [savedRegisters])
  have hread3 : MemReadable t3 (stackPtr t3) 8 := by
    rw [hsp3]
    exact (hRead 24 (by decide)).of_external_eq hm3
  have hc4 : CodeIn (codeRange 0x10322a (encodePopR64 13)) t3 :=
    programText_slice (code.of_external_eq hm3) 0x322a _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨t4, ha4, hr4, he4⟩ :=
    (pop_register_effect_step 0x10322a 13 (by decide)).advances hr3 hc4
      ⟨he3.rip, hread3⟩
      (boundary_ne_program outside (inProgram_of_textOffset 0x322c (by decide)))
  change (popR64Effect 0x10322a 2 13 t3).Holds t3 t4 at he4
  have hm4 : t4.external = t.external :=
    (he4.agrees.external (by simp [Component.Covers])).trans hm3
  have hsp4 : stackPtr t4 = stackPtr s - 16 := by
    have hw : stackPtr t4 = stackPtr t3 + 8 := he4.writes.2
    rw [hw, hsp3]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have hv4 : (Operand.reg 13 : Operand 64).read t4 = s.regValue .r13 := by
    have hw : (Operand.reg 13 : Operand 64).read t4 =
        (Operand.mem (stackPtr t3) : Operand 64).read t3 := he4.writes.1
    rw [hw, hsp3]
    change memLoad t3.external (stackPtr s - 24) 64 = _
    rw [hm3]
    exact state.saved (.r13, 24) (by simp [savedRegisters])
  have hread4 : MemReadable t4 (stackPtr t4) 8 := by
    rw [hsp4]
    exact (hRead 16 (by decide)).of_external_eq hm4
  have hc5 : CodeIn (codeRange 0x10322c (encodePopR64 14)) t4 :=
    programText_slice (code.of_external_eq hm4) 0x322c _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨t5, ha5, hr5, he5⟩ :=
    (pop_register_effect_step 0x10322c 14 (by decide)).advances hr4 hc5
      ⟨he4.rip, hread4⟩
      (boundary_ne_program outside (inProgram_of_textOffset 0x322e (by decide)))
  change (popR64Effect 0x10322c 2 14 t4).Holds t4 t5 at he5
  have hm5 : t5.external = t.external :=
    (he5.agrees.external (by simp [Component.Covers])).trans hm4
  have hsp5 : stackPtr t5 = stackPtr s - 8 := by
    have hw : stackPtr t5 = stackPtr t4 + 8 := he5.writes.2
    rw [hw, hsp4]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have hv5 : (Operand.reg 14 : Operand 64).read t5 = s.regValue .r14 := by
    have hw : (Operand.reg 14 : Operand 64).read t5 =
        (Operand.mem (stackPtr t4) : Operand 64).read t4 := he5.writes.1
    rw [hw, hsp4]
    change memLoad t4.external (stackPtr s - 16) 64 = _
    rw [hm4]
    exact state.saved (.r14, 16) (by simp [savedRegisters])
  have hread5 : MemReadable t5 (stackPtr t5) 8 := by
    rw [hsp5]
    exact (hRead 8 (by decide)).of_external_eq hm5
  have hc6 : CodeIn (codeRange 0x10322e (encodePopR64 15)) t5 :=
    programText_slice (code.of_external_eq hm5) 0x322e _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨t6, ha6, hr6, he6⟩ :=
    (pop_register_effect_step 0x10322e 15 (by decide)).advances hr5 hc6
      ⟨he5.rip, hread5⟩
      (boundary_ne_program outside (inProgram_of_textOffset 0x3230 (by decide)))
  change (popR64Effect 0x10322e 2 15 t5).Holds t5 t6 at he6
  have hm6 : t6.external = t.external :=
    (he6.agrees.external (by simp [Component.Covers])).trans hm5
  have hsp6 : stackPtr t6 = stackPtr s - 0 := by
    have hw : stackPtr t6 = stackPtr t5 + 8 := he6.writes.2
    rw [hw, hsp5]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have hv6 : (Operand.reg 15 : Operand 64).read t6 = s.regValue .r15 := by
    have hw : (Operand.reg 15 : Operand 64).read t6 =
        (Operand.mem (stackPtr t5) : Operand 64).read t5 := he6.writes.1
    rw [hw, hsp5]
    change memLoad t5.external (stackPtr s - 8) 64 = _
    rw [hm5]
    exact state.saved (.r15, 8) (by simp [savedRegisters])
  have hsp6' : stackPtr t6 = stackPtr s := by simpa using hsp6
  have hread6 : MemReadable t6 (stackPtr t6) 8 := by
    rw [hsp6']
    simpa using (hRead 0 (by decide)).of_external_eq hm6
  have htop6 : stackTop t6 = (returnBoundary s).rip := by
    rw [stackTop, hsp6']
    change memLoad t6.external (stackPtr s) 64 = _
    rw [hm6]
    exact state.returnAddress
  have hc7 : CodeIn (codeRange 0x103230 [0xc3]) t6 :=
    programText_slice (code.of_external_eq hm6) 0x3230 _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨u, step, ready, effect⟩ := ret_effect_step 0x103230 t6 hr6 hc7
    ⟨⟨he6.rip, hread6⟩, htop6 ▸ low⟩
  have ret : Returns (returnBoundary s) 1 t6 u := Returns.of_step step
    (effect.rip.trans htop6) (by
      change stackPtr u = stackPtr s + 8
      have hw : stackPtr u = stackPtr t6 + 8 := effect.writes
      rw [hw, hsp6'])
  have frame := (((((he1.agrees.trans he2.agrees).trans he3.agrees).trans he4.agrees).trans he5.agrees).trans he6.agrees).trans effect.agrees
  refine ⟨u, (((((ha1.trans ha2).trans ha3).trans ha4).trans ha5).trans ha6).returns ret,
    supportedMachine_of_ready_agrees state.machine ready frame,
    bindingsSupported_of_ready_agrees state.bindingsSupported ready frame,
    ?_, frame.directionFlagClear (by simp) state.directionFlag,
    frame.external (by simp [Component.Covers]), frame.read (n := 64) (r := 0) (by simp)⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (((((he3.agrees.trans he4.agrees).trans he5.agrees).trans he6.agrees).trans effect.agrees).read (n := 64) (r := 3) (by simp)).trans hv2
  · exact (frame.read (n := 64) (r := 5) (by simp)).trans state.rbp
  · exact ((((he4.agrees.trans he5.agrees).trans he6.agrees).trans effect.agrees).read (n := 64) (r := 12) (by simp)).trans hv3
  · exact (((he5.agrees.trans he6.agrees).trans effect.agrees).read (n := 64) (r := 13) (by simp)).trans hv4
  · exact ((he6.agrees.trans effect.agrees).read (n := 64) (r := 14) (by simp)).trans hv5
  · exact (effect.agrees.read (n := 64) (r := 15) (by simp)).trans hv6

end P256.Proofs.Verifying.Wrapper
