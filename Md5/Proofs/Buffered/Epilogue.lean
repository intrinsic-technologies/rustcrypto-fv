import Md5.Proofs.Block.Entry
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import X86Proofs.Instructions.Pop.Triple
import X86Proofs.Instructions.Call.Triple

namespace Md5.Proofs.Buffered

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Md5.Proofs.Block

theorem digest_epilogue [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hRip : s.RIP = 0x10027b)
    (hSlots : ∀ i < 5, MemReadable s (stackPtr s + BitVec.ofNat 64 (264 + 8 * i)) 8)
    (hReturn : boundary.rip = (Operand.mem (stackPtr s + 296) : Operand 64).read s)
    (hRsp : boundary.rsp = stackPtr s + 304)
    (hLow : boundary.rip.toNat < userAddressLimit)
    (hOutside : ¬ InProgram boundary.rip) :
    ∃ t, Returns boundary 6 s t ∧ ReadyToStep t ∧
      AgreesExcept [.reg 3, .reg 4, .reg 12, .reg 14, .reg 15, .flags, .rip] s t ∧
      t.regValue .rbx = (Operand.mem (stackPtr s + 264) : Operand 64).read s ∧
      t.regValue .r12 = (Operand.mem (stackPtr s + 272) : Operand 64).read s ∧
      t.regValue .r14 = (Operand.mem (stackPtr s + 280) : Operand 64).read s ∧
      t.regValue .r15 = (Operand.mem (stackPtr s + 288) : Operand 64).read s := by
  have hb0 : CodeIn (codeRange 0x10027b [0x48, 0x81, 0xc4, 0x08, 0x01, 0x00, 0x00]) s :=
    program_text_slice hCode 0x27b 7 (by decide +kernel)
  obtain ⟨s1, ha1, hr1, he1⟩ :=
    (add_r64_imm32_effect_step 0x10027b 0x48 0xc4 0x108
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)).advances
      hReady hb0 hRip (text_address_ne_return hOutside 0x282 (by decide +kernel))
  change (addR64Imm32Effect 0x10027b 4 264 s).Holds s s1 at he1
  have hs1 : stackPtr s1 = stackPtr s + 264 := he1.writes
  have hm1 : s1.external = s.external := he1.agrees.external (by simp [Component.Covers])
  have hc1 := he1.codeIn (addR64Imm32Effect_avoids _ _ _ _ _) hCode
  have hb1 : CodeIn (codeRange 0x100282 [0x5b]) s1 :=
    program_text_slice hc1 0x282 1 (by decide +kernel)
  have hp1 : PopPre 0x100282 s1 := by
    refine ⟨he1.rip, ?_⟩
    rw [hs1]
    exact (hSlots 0 (by decide +kernel)).of_external_eq hm1
  obtain ⟨s2, ha2, hr2, he2⟩ :=
    (pop_r64_effect_step 0x100282 0x5b
      (by decide +kernel) (by decide +kernel)).advances hr1 hb1 hp1
      (text_address_ne_return hOutside 0x283 (by decide +kernel))
  change (popR64Effect 0x100282 1 3 s1).Holds s1 s2 at he2
  have hs2 : stackPtr s2 = stackPtr s + 272 := by
    have h := he2.writes.2
    change stackPtr s2 = stackPtr s1 + 8 at h
    rw [hs1, BitVec.add_assoc] at h
    exact h
  have hm2 : s2.external = s.external :=
    (he2.agrees.external (by simp [Component.Covers])).trans hm1
  have hc2 := he2.codeIn (popR64Effect_avoids _ _ _ _ _) hc1
  have hv3 : (Operand.reg 3 : Operand 64).read s2 =
      (Operand.mem (stackPtr s + 264) : Operand 64).read s := by
    have h := he2.writes.1
    simpa only [hs1, Operand.read, hm1] using h
  have hb2 : CodeIn (codeRange 0x100283 [0x41, 0x5c]) s2 :=
    program_text_slice hc2 0x283 2 (by decide +kernel)
  have hp2 : PopPre 0x100283 s2 := by
    refine ⟨he2.rip, ?_⟩
    rw [hs2]
    exact (hSlots 1 (by decide +kernel)).of_external_eq hm2
  obtain ⟨s3, ha3, hr3, he3⟩ :=
    (pop_r64_rex_effect_step 0x100283 0x41 0x5c
      (by unfold RexPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)).advances hr2 hb2 hp2
      (text_address_ne_return hOutside 0x285 (by decide +kernel))
  change (popR64Effect 0x100283 2 12 s2).Holds s2 s3 at he3
  have hs3 : stackPtr s3 = stackPtr s + 280 := by
    have h := he3.writes.2
    change stackPtr s3 = stackPtr s2 + 8 at h
    rw [hs2, BitVec.add_assoc] at h
    exact h
  have hm3 : s3.external = s.external :=
    (he3.agrees.external (by simp [Component.Covers])).trans hm2
  have hc3 := he3.codeIn (popR64Effect_avoids _ _ _ _ _) hc2
  have hv12 : (Operand.reg 12 : Operand 64).read s3 =
      (Operand.mem (stackPtr s + 272) : Operand 64).read s := by
    have h := he3.writes.1
    simpa only [hs2, Operand.read, hm2] using h
  have hb3 : CodeIn (codeRange 0x100285 [0x41, 0x5e]) s3 :=
    program_text_slice hc3 0x285 2 (by decide +kernel)
  have hp3 : PopPre 0x100285 s3 := by
    refine ⟨he3.rip, ?_⟩
    rw [hs3]
    exact (hSlots 2 (by decide +kernel)).of_external_eq hm3
  obtain ⟨s4, ha4, hr4, he4⟩ :=
    (pop_r64_rex_effect_step 0x100285 0x41 0x5e
      (by unfold RexPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)).advances hr3 hb3 hp3
      (text_address_ne_return hOutside 0x287 (by decide +kernel))
  change (popR64Effect 0x100285 2 14 s3).Holds s3 s4 at he4
  have hs4 : stackPtr s4 = stackPtr s + 288 := by
    have h := he4.writes.2
    change stackPtr s4 = stackPtr s3 + 8 at h
    rw [hs3, BitVec.add_assoc] at h
    exact h
  have hm4 : s4.external = s.external :=
    (he4.agrees.external (by simp [Component.Covers])).trans hm3
  have hc4 := he4.codeIn (popR64Effect_avoids _ _ _ _ _) hc3
  have hv14 : (Operand.reg 14 : Operand 64).read s4 =
      (Operand.mem (stackPtr s + 280) : Operand 64).read s := by
    have h := he4.writes.1
    simpa only [hs3, Operand.read, hm3] using h
  have hb4 : CodeIn (codeRange 0x100287 [0x41, 0x5f]) s4 :=
    program_text_slice hc4 0x287 2 (by decide +kernel)
  have hp4 : PopPre 0x100287 s4 := by
    refine ⟨he4.rip, ?_⟩
    rw [hs4]
    exact (hSlots 3 (by decide +kernel)).of_external_eq hm4
  obtain ⟨s5, ha5, hr5, he5⟩ :=
    (pop_r64_rex_effect_step 0x100287 0x41 0x5f
      (by unfold RexPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)).advances hr4 hb4 hp4
      (text_address_ne_return hOutside 0x289 (by decide +kernel))
  change (popR64Effect 0x100287 2 15 s4).Holds s4 s5 at he5
  have hs5 : stackPtr s5 = stackPtr s + 296 := by
    have h := he5.writes.2
    change stackPtr s5 = stackPtr s4 + 8 at h
    rw [hs4, BitVec.add_assoc] at h
    exact h
  have hm5 : s5.external = s.external :=
    (he5.agrees.external (by simp [Component.Covers])).trans hm4
  have hc5 := he5.codeIn (popR64Effect_avoids _ _ _ _ _) hc4
  have hv15 : (Operand.reg 15 : Operand 64).read s5 =
      (Operand.mem (stackPtr s + 288) : Operand 64).read s := by
    have h := he5.writes.1
    simpa only [hs4, Operand.read, hm4] using h
  have hb5 : CodeIn (codeRange 0x100289 [0xc3]) s5 :=
    program_text_slice hc5 0x289 1 (by decide +kernel)
  have ht : stackTop s5 = boundary.rip := by
    rw [hReturn]
    simp only [stackTop, hs5, Operand.read, hm5]
  have hp5 : RetPre 0x100289 s5 := by
    refine ⟨⟨he5.rip, ?_⟩, ?_⟩
    · rw [hs5]
      exact (hSlots 4 (by decide +kernel)).of_external_eq hm5
    · rw [ht]
      exact hLow
  obtain ⟨t, hstep, hr, he⟩ := ret_effect_step 0x100289 s5 hr5 hb5 hp5
  have hret : Returns boundary 1 s5 t := by
    apply Returns.of_step hstep (he.rip.trans ht)
    have h := he.writes
    change stackPtr t = stackPtr s5 + 8 at h
    rw [hs5, BitVec.add_assoc] at h
    exact h.trans hRsp.symm
  have hAll := ((((he1.agrees.trans he2.agrees).trans he3.agrees).trans
    he4.agrees).trans he5.agrees).trans he.agrees
  refine ⟨t, ha1.returns (ha2.returns (ha3.returns (ha4.returns (ha5.returns hret)))),
    hr, hAll.mono (by simp), ?_, ?_, ?_, ?_⟩
  · exact (((he3.agrees.trans he4.agrees).trans he5.agrees).trans he.agrees).read
      (n := 64) (r := 3) (by simp) |>.trans hv3
  · exact ((he4.agrees.trans he5.agrees).trans he.agrees).read
      (n := 64) (r := 12) (by simp) |>.trans hv12
  · exact (he5.agrees.trans he.agrees).read
      (n := 64) (r := 14) (by simp) |>.trans hv14
  · exact he.agrees.read (n := 64) (r := 15) (by simp) |>.trans hv15

end Md5.Proofs.Buffered
