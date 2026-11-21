import P256.Proofs.Program.Pop
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import X86Proofs.Instructions.Call.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem restore [Bindings] {s : RamState} {boundary : ReturnBoundary} {target : BitVec 64}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (outside : ¬ InProgram boundary.rip) (rip : s.RIP = 0x10e194)
    (readable : ∀ off ∈ ([1128,1136,1144,1152,1160,1168,1176] : List Nat),
      MemReadable s (stackPtr s + BitVec.ofNat 64 off) 8)
    (returnWord : memLoad s.external (stackPtr s + 1176) 64 = target)
    (targetInProgram : InProgram target) :
    ∃ t, Advances boundary 8 s t ∧ ReadyToStep t ∧ t.RIP = target ∧
      stackPtr t = stackPtr s + 1184 ∧ t.external = s.external ∧
      AgreesExcept [.reg 3,.reg 4,.reg 5,.reg 12,.reg 13,.reg 14,.reg 15,.flags,.rip] s t ∧
      t.regValue .rbx = memLoad s.external (stackPtr s + 1128) 64 ∧
      t.regValue .r12 = memLoad s.external (stackPtr s + 1136) 64 ∧
      t.regValue .r13 = memLoad s.external (stackPtr s + 1144) 64 ∧
      t.regValue .r14 = memLoad s.external (stackPtr s + 1152) 64 ∧
      t.regValue .r15 = memLoad s.external (stackPtr s + 1160) 64 ∧
      t.regValue .rbp = memLoad s.external (stackPtr s + 1168) 64 := by
  obtain ⟨s0, a0, r0, e0⟩ :=
    (add_r64_imm32_effect_step 0x10e194 0x48 0xc4 1128
      (by simp [RexWPrefix]) rfl rfl).advances ready
      (programText_slice (programLoaded_codeIn loaded) 0xe194 _
        (by decide) (by decide +kernel)) rip
      (boundary_ne_program outside (inProgram_of_textOffset 0xe19b (by decide)))
  have g0 : AgreesExcept [.reg 4,.flags,.rip] s s0 := e0.agrees
  have m0 : s0.external = s.external := g0.external (by simp [Component.Covers])
  have sp0 : stackPtr s0 = stackPtr s + 1128 := e0.writes
  obtain ⟨s1, a1, r1, e1⟩ :=
    (pop_register_effect_step 0x10e19b 3 (by decide)).advances r0
      (programText_slice ((programLoaded_codeIn loaded).of_external_eq m0) 0xe19b
        (encodePopR64 3) (by decide) (by decide +kernel))
      ⟨e0.rip, by rw [sp0]; exact (readable 1128 (by simp)).of_external_eq m0⟩
      (boundary_ne_program outside (inProgram_of_textOffset 0xe19c (by decide)))
  have g1 : AgreesExcept [.reg 3, .reg 4, .rip] s0 s1 := e1.agrees
  have m1 : s1.external = s.external :=
    (g1.external (by simp [Component.Covers])).trans m0
  have sp1 : stackPtr s1 = stackPtr s + 1136 := by
    have hw : stackPtr s1 = stackPtr s0 + 8 := e1.writes.2
    rw [hw, sp0, BitVec.add_assoc]
    rfl
  have v1 : s1.regValue .rbx = memLoad s.external (stackPtr s + 1128) 64 := by
    have hw : s1.regValue .rbx = memLoad s0.external (stackPtr s0) 64 := e1.writes.1
    rwa [m0, sp0] at hw
  obtain ⟨s2, a2, r2, e2⟩ :=
    (pop_register_effect_step 0x10e19c 12 (by decide)).advances r1
      (programText_slice ((programLoaded_codeIn loaded).of_external_eq m1) 0xe19c
        (encodePopR64 12) (by decide) (by decide +kernel))
      ⟨e1.rip, by rw [sp1]; exact (readable 1136 (by simp)).of_external_eq m1⟩
      (boundary_ne_program outside (inProgram_of_textOffset 0xe19e (by decide)))
  have g2 : AgreesExcept [.reg 12, .reg 4, .rip] s1 s2 := e2.agrees
  have m2 : s2.external = s.external :=
    (g2.external (by simp [Component.Covers])).trans m1
  have sp2 : stackPtr s2 = stackPtr s + 1144 := by
    have hw : stackPtr s2 = stackPtr s1 + 8 := e2.writes.2
    rw [hw, sp1, BitVec.add_assoc]
    rfl
  have v2 : s2.regValue .r12 = memLoad s.external (stackPtr s + 1136) 64 := by
    have hw : s2.regValue .r12 = memLoad s1.external (stackPtr s1) 64 := e2.writes.1
    rwa [m1, sp1] at hw
  obtain ⟨s3, a3, r3, e3⟩ :=
    (pop_register_effect_step 0x10e19e 13 (by decide)).advances r2
      (programText_slice ((programLoaded_codeIn loaded).of_external_eq m2) 0xe19e
        (encodePopR64 13) (by decide) (by decide +kernel))
      ⟨e2.rip, by rw [sp2]; exact (readable 1144 (by simp)).of_external_eq m2⟩
      (boundary_ne_program outside (inProgram_of_textOffset 0xe1a0 (by decide)))
  have g3 : AgreesExcept [.reg 13, .reg 4, .rip] s2 s3 := e3.agrees
  have m3 : s3.external = s.external :=
    (g3.external (by simp [Component.Covers])).trans m2
  have sp3 : stackPtr s3 = stackPtr s + 1152 := by
    have hw : stackPtr s3 = stackPtr s2 + 8 := e3.writes.2
    rw [hw, sp2, BitVec.add_assoc]
    rfl
  have v3 : s3.regValue .r13 = memLoad s.external (stackPtr s + 1144) 64 := by
    have hw : s3.regValue .r13 = memLoad s2.external (stackPtr s2) 64 := e3.writes.1
    rwa [m2, sp2] at hw
  obtain ⟨s4, a4, r4, e4⟩ :=
    (pop_register_effect_step 0x10e1a0 14 (by decide)).advances r3
      (programText_slice ((programLoaded_codeIn loaded).of_external_eq m3) 0xe1a0
        (encodePopR64 14) (by decide) (by decide +kernel))
      ⟨e3.rip, by rw [sp3]; exact (readable 1152 (by simp)).of_external_eq m3⟩
      (boundary_ne_program outside (inProgram_of_textOffset 0xe1a2 (by decide)))
  have g4 : AgreesExcept [.reg 14, .reg 4, .rip] s3 s4 := e4.agrees
  have m4 : s4.external = s.external :=
    (g4.external (by simp [Component.Covers])).trans m3
  have sp4 : stackPtr s4 = stackPtr s + 1160 := by
    have hw : stackPtr s4 = stackPtr s3 + 8 := e4.writes.2
    rw [hw, sp3, BitVec.add_assoc]
    rfl
  have v4 : s4.regValue .r14 = memLoad s.external (stackPtr s + 1152) 64 := by
    have hw : s4.regValue .r14 = memLoad s3.external (stackPtr s3) 64 := e4.writes.1
    rwa [m3, sp3] at hw
  obtain ⟨s5, a5, r5, e5⟩ :=
    (pop_register_effect_step 0x10e1a2 15 (by decide)).advances r4
      (programText_slice ((programLoaded_codeIn loaded).of_external_eq m4) 0xe1a2
        (encodePopR64 15) (by decide) (by decide +kernel))
      ⟨e4.rip, by rw [sp4]; exact (readable 1160 (by simp)).of_external_eq m4⟩
      (boundary_ne_program outside (inProgram_of_textOffset 0xe1a4 (by decide)))
  have g5 : AgreesExcept [.reg 15, .reg 4, .rip] s4 s5 := e5.agrees
  have m5 : s5.external = s.external :=
    (g5.external (by simp [Component.Covers])).trans m4
  have sp5 : stackPtr s5 = stackPtr s + 1168 := by
    have hw : stackPtr s5 = stackPtr s4 + 8 := e5.writes.2
    rw [hw, sp4, BitVec.add_assoc]
    rfl
  have v5 : s5.regValue .r15 = memLoad s.external (stackPtr s + 1160) 64 := by
    have hw : s5.regValue .r15 = memLoad s4.external (stackPtr s4) 64 := e5.writes.1
    rwa [m4, sp4] at hw
  obtain ⟨s6, a6, r6, e6⟩ :=
    (pop_register_effect_step 0x10e1a4 5 (by decide)).advances r5
      (programText_slice ((programLoaded_codeIn loaded).of_external_eq m5) 0xe1a4
        (encodePopR64 5) (by decide) (by decide +kernel))
      ⟨e5.rip, by rw [sp5]; exact (readable 1168 (by simp)).of_external_eq m5⟩
      (boundary_ne_program outside (inProgram_of_textOffset 0xe1a5 (by decide)))
  have g6 : AgreesExcept [.reg 5, .reg 4, .rip] s5 s6 := e6.agrees
  have m6 : s6.external = s.external :=
    (g6.external (by simp [Component.Covers])).trans m5
  have sp6 : stackPtr s6 = stackPtr s + 1176 := by
    have hw : stackPtr s6 = stackPtr s5 + 8 := e6.writes.2
    rw [hw, sp5, BitVec.add_assoc]
    rfl
  have v6 : s6.regValue .rbp = memLoad s.external (stackPtr s + 1168) 64 := by
    have hw : s6.regValue .rbp = memLoad s5.external (stackPtr s5) 64 := e6.writes.1
    rwa [m5, sp5] at hw
  have top : stackTop s6 = target := by
    change memLoad s6.external (stackPtr s6) 64 = target
    rw [m6, sp6]
    exact returnWord
  obtain ⟨t, a7, r7, e7⟩ := (ret_effect_step 0x10e1a5).advances r6
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq m6) 0xe1a5 [0xc3]
      (by decide) (by decide +kernel))
    ⟨⟨e6.rip, by rw [sp6]; exact (readable 1176 (by simp)).of_external_eq m6⟩,
      top ▸ inProgram_low targetInProgram⟩
    (by change stackTop s6 ≠ boundary.rip
        rw [top]
        exact boundary_ne_program outside targetInProgram)
  have g7 : AgreesExcept [.reg 4,.rip] s6 t := e7.agrees
  have sp7 : stackPtr t = stackPtr s + 1184 := by
    have hw : stackPtr t = stackPtr s6 + 8 := e7.writes
    rw [hw, sp6, BitVec.add_assoc]
    rfl
  refine ⟨t, ((((((a0.trans a1).trans a2).trans a3).trans a4).trans a5).trans a6).trans a7,
    r7, e7.rip.trans top, sp7, (g7.external (by simp [Component.Covers])).trans m6,
    ((((((g0.trans g1).trans g2).trans g3).trans g4).trans g5).trans g6).trans g7 |>.mono (by simp),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((((((g2.trans g3).trans g4).trans g5).trans g6).trans g7).read (n := 64) (r := 3) (by simp)).trans v1
  · exact (((((g3.trans g4).trans g5).trans g6).trans g7).read (n := 64) (r := 12) (by simp)).trans v2
  · exact ((((g4.trans g5).trans g6).trans g7).read (n := 64) (r := 13) (by simp)).trans v3
  · exact (((g5.trans g6).trans g7).read (n := 64) (r := 14) (by simp)).trans v4
  · exact ((g6.trans g7).read (n := 64) (r := 15) (by simp)).trans v5
  · exact (g7.read (n := 64) (r := 5) (by simp)).trans v6

end P256.Proofs.Verifying.Message
