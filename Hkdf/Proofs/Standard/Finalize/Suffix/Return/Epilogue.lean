import Hkdf.Proofs.Common.Memory.Copy.Return
import Hkdf.Proofs.Standard.Finalize.Suffix.State
import Hkdf.Proofs.Common.Encoding.Serialize.Stack
import Hkdf.Proofs.Common.Encoding.Serialize.Tail.Epilogue
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Call.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Finalize.Suffix.Return

open Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.Machine

theorem savedMemory_register (initial : RamState) (entry : Syntax.Reg × Nat)
    (member : entry ∈ [(.rbx, 40), (.r12, 32), (.r13, 24), (.r14, 16), (.r15, 8)]) :
    memLoad (Hmac.savedMemory initial) (stackPtr initial - BitVec.ofNat 64 entry.2) 64 =
      initial.regValue entry.1 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [Hmac.savedMemory, BitVec.sub_eq_add_neg]
    repeat first
      | rw [memLoad_memStore_apart _ _ _ _ _ 64
          (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)]
      | exact memLoad_memStore _ _ (by decide) (by decide) _

theorem epilogue [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre initial boundary 0x10dd90 144 176 1264)
    (state : Suffix.State initial boundary s) (rip : s.RIP = 0x10e28a) :
    ∃ t, CalleeResult initial t boundary 176 1264 ∧ t.external = s.external := by
  have saved (entry : Syntax.Reg × Nat)
      (member : entry ∈ [(.rbx, 40), (.r12, 32), (.r13, 24), (.r14, 16), (.r15, 8)]) :
      memLoad s.external (stackPtr initial - BitVec.ofNat 64 entry.2) 64 =
        initial.regValue entry.1 := by
    rw [← savedMemory_register initial entry member]
    apply memLoad_congr
    intro i hi
    change (s.external[_]?).getD 0 = ((Hmac.savedMemory initial)[_]?).getD 0
    have bound : entry.2 ≤ 40 ∧ 8 ≤ entry.2 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl <;> decide
    have eq : stackPtr initial - BitVec.ofNat 64 entry.2 + BitVec.ofNat 64 i =
        stackPtr initial - 40 + BitVec.ofNat 64 (40 - entry.2 + i) := by
      rw [BitVec.ofNat_add, ← BitVec.ofNat_sub_ofNat_of_le 40 entry.2 (by omega) bound.1]
      simp only [BitVec.ofNat_eq_ofNat, BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rw [← BitVec.add_assoc (-(BitVec.ofNat 64 40)) (BitVec.ofNat 64 40),
        BitVec.add_left_neg, BitVec.zero_add]
    rw [eq, state.saved _ (by omega)]
  have savedReturn : memLoad s.external (stackPtr initial) 64 =
      (returnBoundary initial).rip := by
    change memLoad s.external (stackPtr initial) 64 = memLoad initial.external (stackPtr initial) 64
    have same : memLoad s.external (stackPtr initial) 64 =
        memLoad (Hmac.savedMemory initial) (stackPtr initial) 64 := by
      apply memLoad_congr
      intro i hi
      change (s.external[_]?).getD 0 = ((Hmac.savedMemory initial)[_]?).getD 0
      have eq : stackPtr initial + BitVec.ofNat 64 i =
          stackPtr initial - 40 + BitVec.ofNat 64 (40 + i) := by
        rw [BitVec.ofNat_add]
        simp only [BitVec.ofNat_eq_ofNat, ← BitVec.add_assoc, BitVec.sub_add_cancel]
      rw [eq, state.saved _ (by omega)]
    rw [same]
    simp only [Hmac.savedMemory, BitVec.sub_eq_add_neg]
    repeat rw [memLoad_memStore_apart_right _ _ _ _ 64
      (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)]
  have code := programLoaded_codeIn state.running.loaded
  have hRead (offset : Nat) (ho : offset ≤ 1264) :
      MemReadable s (stackPtr initial - BitVec.ofNat 64 offset) 8 :=
    Hkdf.Proofs.Common.Encoding.Serialize.readable_of_grow (Hkdf.Proofs.Common.Encoding.Serialize.stack_sub_readable pre ho (by omega)) state.running.allocated
  have hc0 : CodeIn (codeRange 0x10e28a [0x48, 0x89, 0xd8]) s :=
    programText_slice code 0xe28a _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t0, ha0, hr0, he0⟩ :=
    (mov_r64_r64_effect_step 0x10e28a 0x48 0xd8
      (by simp [RexWPrefix]) rfl).advances
      (supportedMachine_readyToStep state.running.machine) hc0
      rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe28d (by decide)))
  change (movR64R64Effect 0x10e28a 0 3 s).Holds s t0 at he0
  have hm0 : t0.external = s.external := he0.agrees.external (by simp [Component.Covers])
  have sp0 : stackPtr t0 = stackPtr s := he0.agrees.read (n := 64) (r := 4) (by simp)
  have hc1 : CodeIn (codeRange 0x10e28d [0x48, 0x81, 0xc4, 0x70, 1, 0, 0]) t0 :=
    programText_slice (code.of_external_eq hm0) 0xe28d _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t1, ha1, hr1, he1⟩ :=
    (add_r64_imm32_effect_step 0x10e28d 0x48 0xc4 368
      (by simp [RexWPrefix]) (by decide) (by decide)).advances
      hr0 hc1 he0.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe294 (by decide)))
  change (addR64Imm32Effect 0x10e28d 4 368 t0).Holds t0 t1 at he1
  have hm1 : t1.external = s.external := (he1.agrees.external (by simp [Component.Covers])).trans hm0
  have hsp1 : stackPtr t1 = stackPtr initial - 40 := by
    have hw : stackPtr t1 = stackPtr t0 + 368 := he1.writes
    rw [hw, sp0, state.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have hread1 : MemReadable t1 (stackPtr t1) 8 := by
    rw [hsp1]
    exact (hRead 40 (by decide)).of_external_eq hm1
  have hc2 : CodeIn (codeRange 0x10e294 (encodePopR64 3)) t1 :=
    programText_slice (code.of_external_eq hm1) 0xe294 _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨t2, ha2, hr2, he2⟩ :=
    (Hkdf.Proofs.Common.Encoding.Serialize.pop_register_effect_step 0x10e294 3 (by decide)).advances hr1 hc2
      ⟨he1.rip, hread1⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe295 (by decide)))
  change (popR64Effect 0x10e294 1 3 t1).Holds t1 t2 at he2
  have hm2 : t2.external = s.external :=
    (he2.agrees.external (by simp [Component.Covers])).trans hm1
  have hsp2 : stackPtr t2 = stackPtr initial - 32 := by
    have hw : stackPtr t2 = stackPtr t1 + 8 := he2.writes.2
    rw [hw, hsp1]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have hv2 : (Operand.reg 3 : Operand 64).read t2 = initial.regValue .rbx := by
    have hw : (Operand.reg 3 : Operand 64).read t2 =
        (Operand.mem (stackPtr t1) : Operand 64).read t1 := he2.writes.1
    rw [hw, hsp1]
    change memLoad t1.external (stackPtr initial - 40) 64 = _
    rw [hm1]
    exact saved (.rbx, 40) (by simp)
  have hread2 : MemReadable t2 (stackPtr t2) 8 := by
    rw [hsp2]
    exact (hRead 32 (by decide)).of_external_eq hm2
  have hc3 : CodeIn (codeRange 0x10e295 (encodePopR64 12)) t2 :=
    programText_slice (code.of_external_eq hm2) 0xe295 _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨t3, ha3, hr3, he3⟩ :=
    (Hkdf.Proofs.Common.Encoding.Serialize.pop_register_effect_step 0x10e295 12 (by decide)).advances hr2 hc3
      ⟨he2.rip, hread2⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe297 (by decide)))
  change (popR64Effect 0x10e295 2 12 t2).Holds t2 t3 at he3
  have hm3 : t3.external = s.external :=
    (he3.agrees.external (by simp [Component.Covers])).trans hm2
  have hsp3 : stackPtr t3 = stackPtr initial - 24 := by
    have hw : stackPtr t3 = stackPtr t2 + 8 := he3.writes.2
    rw [hw, hsp2]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have hv3 : (Operand.reg 12 : Operand 64).read t3 = initial.regValue .r12 := by
    have hw : (Operand.reg 12 : Operand 64).read t3 =
        (Operand.mem (stackPtr t2) : Operand 64).read t2 := he3.writes.1
    rw [hw, hsp2]
    change memLoad t2.external (stackPtr initial - 32) 64 = _
    rw [hm2]
    exact saved (.r12, 32) (by simp)
  have hread3 : MemReadable t3 (stackPtr t3) 8 := by
    rw [hsp3]
    exact (hRead 24 (by decide)).of_external_eq hm3
  have hc4 : CodeIn (codeRange 0x10e297 (encodePopR64 13)) t3 :=
    programText_slice (code.of_external_eq hm3) 0xe297 _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨t4, ha4, hr4, he4⟩ :=
    (Hkdf.Proofs.Common.Encoding.Serialize.pop_register_effect_step 0x10e297 13 (by decide)).advances hr3 hc4
      ⟨he3.rip, hread3⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe299 (by decide)))
  change (popR64Effect 0x10e297 2 13 t3).Holds t3 t4 at he4
  have hm4 : t4.external = s.external :=
    (he4.agrees.external (by simp [Component.Covers])).trans hm3
  have hsp4 : stackPtr t4 = stackPtr initial - 16 := by
    have hw : stackPtr t4 = stackPtr t3 + 8 := he4.writes.2
    rw [hw, hsp3]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have hv4 : (Operand.reg 13 : Operand 64).read t4 = initial.regValue .r13 := by
    have hw : (Operand.reg 13 : Operand 64).read t4 =
        (Operand.mem (stackPtr t3) : Operand 64).read t3 := he4.writes.1
    rw [hw, hsp3]
    change memLoad t3.external (stackPtr initial - 24) 64 = _
    rw [hm3]
    exact saved (.r13, 24) (by simp)
  have hread4 : MemReadable t4 (stackPtr t4) 8 := by
    rw [hsp4]
    exact (hRead 16 (by decide)).of_external_eq hm4
  have hc5 : CodeIn (codeRange 0x10e299 (encodePopR64 14)) t4 :=
    programText_slice (code.of_external_eq hm4) 0xe299 _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨t5, ha5, hr5, he5⟩ :=
    (Hkdf.Proofs.Common.Encoding.Serialize.pop_register_effect_step 0x10e299 14 (by decide)).advances hr4 hc5
      ⟨he4.rip, hread4⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe29b (by decide)))
  change (popR64Effect 0x10e299 2 14 t4).Holds t4 t5 at he5
  have hm5 : t5.external = s.external :=
    (he5.agrees.external (by simp [Component.Covers])).trans hm4
  have hsp5 : stackPtr t5 = stackPtr initial - 8 := by
    have hw : stackPtr t5 = stackPtr t4 + 8 := he5.writes.2
    rw [hw, hsp4]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have hv5 : (Operand.reg 14 : Operand 64).read t5 = initial.regValue .r14 := by
    have hw : (Operand.reg 14 : Operand 64).read t5 =
        (Operand.mem (stackPtr t4) : Operand 64).read t4 := he5.writes.1
    rw [hw, hsp4]
    change memLoad t4.external (stackPtr initial - 16) 64 = _
    rw [hm4]
    exact saved (.r14, 16) (by simp)
  have hread5 : MemReadable t5 (stackPtr t5) 8 := by
    rw [hsp5]
    exact (hRead 8 (by decide)).of_external_eq hm5
  have hc6 : CodeIn (codeRange 0x10e29b (encodePopR64 15)) t5 :=
    programText_slice (code.of_external_eq hm5) 0xe29b _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨t6, ha6, hr6, he6⟩ :=
    (Hkdf.Proofs.Common.Encoding.Serialize.pop_register_effect_step 0x10e29b 15 (by decide)).advances hr5 hc6
      ⟨he5.rip, hread5⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe29d (by decide)))
  change (popR64Effect 0x10e29b 2 15 t5).Holds t5 t6 at he6
  have hm6 : t6.external = s.external :=
    (he6.agrees.external (by simp [Component.Covers])).trans hm5
  have hsp6 : stackPtr t6 = stackPtr initial - 0 := by
    have hw : stackPtr t6 = stackPtr t5 + 8 := he6.writes.2
    rw [hw, hsp5]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have hv6 : (Operand.reg 15 : Operand 64).read t6 = initial.regValue .r15 := by
    have hw : (Operand.reg 15 : Operand 64).read t6 =
        (Operand.mem (stackPtr t5) : Operand 64).read t5 := he6.writes.1
    rw [hw, hsp5]
    change memLoad t5.external (stackPtr initial - 8) 64 = _
    rw [hm5]
    exact saved (.r15, 8) (by simp)
  have hsp6' : stackPtr t6 = stackPtr initial := by simpa only [BitVec.ofNat_eq_ofNat, BitVec.sub_zero] using hsp6
  have hread6 : MemReadable t6 (stackPtr t6) 8 := by
    rw [hsp6']
    simpa only [BitVec.sub_zero] using (hRead 0 (by decide)).of_external_eq hm6
  have htop6 : stackTop t6 = (returnBoundary initial).rip := by
    rw [stackTop, hsp6']
    change memLoad t6.external (stackPtr initial) 64 = _
    rw [hm6]
    exact savedReturn
  have hc8 : CodeIn (codeRange 0x10e29d [0xc3]) t6 :=
    programText_slice (code.of_external_eq hm6) 0xe29d _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨t, ha8, hr8, he8⟩ := (ret_effect_step 0x10e29d).advances hr6 hc8
    ⟨⟨he6.rip, hread6⟩, htop6 ▸ Hkdf.Proofs.Common.Memory.Copy.inProgram_low pre.returnInProgram⟩
    (by change stackTop t6 ≠ boundary.rip
        rw [htop6]
        exact boundary_ne_program pre.outerBoundary pre.returnInProgram)
  have hm8 : t.external = s.external :=
    (he8.agrees.external (by simp [Component.Covers])).trans hm6
  have hf := (((((((he0.agrees.trans he1.agrees).trans he2.agrees).trans he3.agrees).trans he4.agrees).trans he5.agrees).trans he6.agrees).trans he8.agrees)
  obtain ⟨fuel, hexec⟩ := state.running.execution
  refine ⟨t, ?_, hm8⟩
  refine ⟨⟨fuel + 8, ?_⟩, he8.rip.trans htop6, ?_,
    supportedMachine_of_ready_agrees state.running.machine hr8 hf, ?_, ?_, ?_, ?_⟩
  · exact ((((((((hexec.trans ha0).trans ha1).trans ha2).trans ha3).trans ha4).trans ha5).trans ha6).trans ha8)
  · change stackPtr t = stackPtr initial + 8
    have hw : stackPtr t = stackPtr t6 + 8 := he8.writes
    rw [hw, hsp6']
  · refine ⟨?_, hf.directionFlagClear (by simp) state.running.directionFlag,
      (hf.mxcsr (by simp)).trans state.mxcsr,
      (hf.fcw (by simp)).trans state.fcw⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (Operand.reg 3 : Operand 64).read t = _
      rw [he8.agrees.read (by simp), he6.agrees.read (by simp), he5.agrees.read (by simp), he4.agrees.read (by simp), he3.agrees.read (by simp)]
      exact hv2
    · exact (hf.read (n := 64) (r := 5) (by simp)).trans state.rbp
    · change (Operand.reg 12 : Operand 64).read t = _
      rw [he8.agrees.read (by simp), he6.agrees.read (by simp), he5.agrees.read (by simp), he4.agrees.read (by simp)]
      exact hv3
    · change (Operand.reg 13 : Operand 64).read t = _
      rw [he8.agrees.read (by simp), he6.agrees.read (by simp), he5.agrees.read (by simp)]
      exact hv4
    · change (Operand.reg 14 : Operand 64).read t = _
      rw [he8.agrees.read (by simp), he6.agrees.read (by simp)]
      exact hv5
    · change (Operand.reg 15 : Operand 64).read t = _
      rw [he8.agrees.read (by simp)]
      exact hv6
  · intro address hout
    rw [hm8]
    exact state.running.frame address hout
  · intro address byte hfetch
    rw [hm8]
    exact state.running.loaded address byte hfetch
  · intro address ha
    rw [hm8]
    exact state.running.allocated address ha


end Hkdf.Proofs.Standard.Finalize.Suffix.Return
