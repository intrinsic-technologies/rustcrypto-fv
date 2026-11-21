import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Mov.Triple
import P256.Proofs.Program.Code
import P256.Proofs.Common.Memory.Copy.RegisterOps.Cmov
import P256.Proofs.Common.Instructions.ShiftLeft.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple

set_option autoImplicit false

open P256.Proofs.Common.Instructions.ShiftLeft (shlR64Effect shl_r64_imm8_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice)

namespace P256.Proofs.ReadBe.Entry

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem start_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (rip : s.RIP = 0x1190fa)
    (count : s.regValue .rsi = 32) (limbs : s.regValue .rbp = 4)
    (outside : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 5 s t ∧ ReadyToStep t ∧ t.RIP = 0x11914e ∧
      t.regValue .rbp = 32 ∧ t.regValue .r12 = s.regValue .rdi + 32 ∧
      t.regValue .r15 = 0 ∧ AgreesExcept [.reg 5,.reg 12,.reg 15,.flags,.rip] s t := by
  have code := programLoaded_codeIn loaded
  obtain ⟨s1, a1, r1, e1⟩ :=
    (mov_r64_r64_effect_step 0x1190fa 0x49 0xfc (by simp [RexWPrefix]) rfl).advances ready
      (programText_slice code 0x190fa _ (by decide +kernel) (by decide +kernel)) rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x190fd (by decide)))
  change (movR64R64Effect 0x1190fa 12 7 s).Holds s s1 at e1
  have f1 : AgreesExcept [.reg 12,.rip] s s1 := e1.agrees
  have m1 := f1.external (by simp [Component.Covers])
  have source1 : s1.regValue .r12 = s.regValue .rdi := e1.writes
  have si1 : s1.regValue .rsi = 32 := (f1.read (n := 64) (r := 6) (by simp)).trans count
  obtain ⟨s2, a2, r2, e2⟩ :=
    (add_r64_r64_effect_step 0x1190fd 0x49 0xf4 (by simp [RexWPrefix]) rfl).advances r1
      (programText_slice (code.of_external_eq m1) 0x190fd _ (by decide +kernel) (by decide +kernel)) e1.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x19100 (by decide)))
  change (addR64R64Effect 0x1190fd 12 6 s1).Holds s1 s2 at e2
  have f2 : AgreesExcept [.reg 12,.flags,.rip] s1 s2 := e2.agrees
  have m2 := (f2.external (by simp [Component.Covers])).trans m1
  have source2 : s2.regValue .r12 = s.regValue .rdi + 32 := by
    have h : s2.regValue .r12 = s1.regValue .r12 + s1.regValue .rsi := e2.writes
    rwa [source1, si1] at h
  have bp2 : s2.regValue .rbp = 4 := ((f1.trans f2).read (n := 64) (r := 5) (by simp)).trans limbs
  obtain ⟨s3, a3, r3, e3⟩ :=
    (shl_r64_imm8_effect_step 0x119100 0x48 0xe5 3 (by simp [RexWPrefix]) rfl rfl).advances r2
      (programText_slice (code.of_external_eq m2) 0x19100 _ (by decide +kernel) (by decide +kernel)) e2.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x19104 (by decide)))
  change (shlR64Effect 0x119100 4 5 3 s2).Holds s2 s3 at e3
  have f3 : AgreesExcept [.reg 5,.flags,.rip] s2 s3 := e3.agrees
  have m3 := (f3.external (by simp [Component.Covers])).trans m2
  have bp3 : s3.regValue .rbp = 32 := by
    have h : s3.regValue .rbp = s2.regValue .rbp <<< 3 := e3.writes
    rwa [bp2] at h
  obtain ⟨s4, a4, r4, e4⟩ :=
    (xor_r32_r32_rex_effect_step 0x119104 0x45 0xff (by simp [RexNoWPrefix]) rfl).advances r3
      (programText_slice (code.of_external_eq m3) 0x19104 _ (by decide +kernel) (by decide +kernel)) e3.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x19107 (by decide)))
  change (xorR32R32Effect 0x119104 3 15 15 s3).Holds s3 s4 at e4
  have f4 : AgreesExcept [.reg 15,.flags,.rip] s3 s4 := e4.agrees
  have m4 := (f4.external (by simp [Component.Covers])).trans m3
  have offset4 : s4.regValue .r15 = 0 := by
    have h : s4.regValue .r15 = ((s3.regValue .r15).setWidth 32 ^^^ (s3.regValue .r15).setWidth 32).setWidth 64 := e4.writes
    rw [BitVec.xor_self] at h
    exact h
  obtain ⟨t, a5, r5, e5⟩ :=
    (jmp_rel8_effect_step 0x119107 0x45 (by decide +kernel)).advances r4
      (programText_slice (code.of_external_eq m4) 0x19107 _ (by decide +kernel) (by decide +kernel)) e4.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x1914e (by decide)))
  have f5 : AgreesExcept [.rip] s4 t := e5.agrees
  refine ⟨t, a1.trans (a2.trans (a3.trans (a4.trans a5))), r5, e5.rip, ?_, ?_, ?_, ?_⟩
  · exact ((f4.trans f5).read (n := 64) (r := 5) (by simp)).trans bp3
  · exact (((f3.trans f4).trans f5).read (n := 64) (r := 12) (by simp)).trans source2
  · exact (f5.read (n := 64) (r := 15) (by simp)).trans offset4
  · exact ((((f1.trans f2).trans f3).trans f4).trans f5).mono (by simp)

end P256.Proofs.ReadBe.Entry
