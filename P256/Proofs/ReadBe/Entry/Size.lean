import P256.Proofs.Program.Code
import P256.Proofs.ReadBe.Interface
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple

set_option autoImplicit false

open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice)

namespace P256.Proofs.ReadBe.Entry

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem size_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (rip : s.RIP = 0x1190b9)
    (bits : s.regValue .r8 = 256) (outside : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 7 s t ∧ ReadyToStep t ∧ t.RIP = 0x1190d1 ∧
      t.regValue .r13 = 32 ∧ AgreesExcept [.reg 0,.reg 13,.flags,.rip] s t := by
  have code := programLoaded_codeIn loaded
  obtain ⟨s1, a1, r1, e1⟩ :=
    (mov_r32_r32_rex_effect_step 0x1190b9 0x44 0xc0 (by simp [RexNoWPrefix]) rfl).advances ready
      (programText_slice code 0x190b9 _ (by decide +kernel) (by decide +kernel)) rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x190bc (by decide)))
  change (movR32R32Effect 0x1190b9 3 0 8 s).Holds s s1 at e1
  have f1 : AgreesExcept [.reg 0,.rip] s s1 := e1.agrees
  have m1 := f1.external (by simp [Component.Covers])
  have ax1 : s1.regValue .rax = 256 := by
    have h : s1.regValue .rax = ((s.regValue .r8).setWidth 32).setWidth 64 := e1.writes
    rwa [bits] at h
  obtain ⟨s2, a2, r2, e2⟩ :=
    (shr_r32_imm8_effect_step 0x1190bc 0xe8 3 rfl rfl).advances r1
      (programText_slice (code.of_external_eq m1) 0x190bc _ (by decide +kernel) (by decide +kernel)) e1.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x190bf (by decide)))
  change (shrR32Effect 0x1190bc 3 0 3 s1).Holds s1 s2 at e2
  have f2 : AgreesExcept [.reg 0,.flags,.rip] s1 s2 := e2.agrees
  have m2 := (f2.external (by simp [Component.Covers])).trans m1
  have ax2 : s2.regValue .rax = 32 := by
    have h : s2.regValue .rax = ((s1.regValue .rax).setWidth 32 >>> 3).setWidth 64 := e2.writes
    rwa [ax1] at h
  have r82 : s2.regValue .r8 = 256 := ((f1.trans f2).read (n := 64) (r := 8) (by simp)).trans bits
  obtain ⟨s3, a3, r3, e3⟩ :=
    (mov_r32_r32_rex_effect_step 0x1190bf 0x45 0xc5 (by simp [RexNoWPrefix]) rfl).advances r2
      (programText_slice (code.of_external_eq m2) 0x190bf _ (by decide +kernel) (by decide +kernel)) e2.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x190c2 (by decide)))
  change (movR32R32Effect 0x1190bf 3 13 8 s2).Holds s2 s3 at e3
  have f3 : AgreesExcept [.reg 13,.rip] s2 s3 := e3.agrees
  have m3 := (f3.external (by simp [Component.Covers])).trans m2
  have v3 : s3.regValue .r13 = 256 := by
    have h : s3.regValue .r13 = ((s2.regValue .r8).setWidth 32).setWidth 64 := e3.writes
    rwa [r82] at h
  obtain ⟨s4, a4, r4, e4⟩ :=
    (and_r32_imm8_rex_effect_step 0x1190c2 0x41 0xe5 7 (by simp [RexNoWPrefix]) rfl rfl).advances r3
      (programText_slice (code.of_external_eq m3) 0x190c2 _ (by decide +kernel) (by decide +kernel)) e3.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x190c6 (by decide)))
  change (andR32Imm8Effect 0x1190c2 4 13 7 s3).Holds s3 s4 at e4
  have f4 : AgreesExcept [.reg 13,.flags,.rip] s3 s4 := e4.agrees
  have m4 := (f4.external (by simp [Component.Covers])).trans m3
  have v4 : s4.regValue .r13 = 0 := by
    have h : s4.regValue .r13 = ((s3.regValue .r13).setWidth 32 &&& 7).setWidth 64 := e4.writes
    rwa [v3] at h
  obtain ⟨s5, a5, r5, e5⟩ :=
    (add_r32_imm8_rex_effect_step 0x1190c6 0x41 0xc5 7 (by simp [RexNoWPrefix]) rfl rfl).advances r4
      (programText_slice (code.of_external_eq m4) 0x190c6 _ (by decide +kernel) (by decide +kernel)) e4.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x190ca (by decide)))
  change (addR32Imm8Effect 0x1190c6 4 13 7 s4).Holds s4 s5 at e5
  have f5 : AgreesExcept [.reg 13,.flags,.rip] s4 s5 := e5.agrees
  have m5 := (f5.external (by simp [Component.Covers])).trans m4
  have v5 : s5.regValue .r13 = 7 := by
    have h : s5.regValue .r13 = ((s4.regValue .r13).setWidth 32 + 7).setWidth 64 := e5.writes
    rwa [v4] at h
  obtain ⟨s6, a6, r6, e6⟩ :=
    (shr_r32_imm8_rex_effect_step 0x1190ca 0x41 0xed 3 (by simp [RexNoWPrefix]) rfl rfl).advances r5
      (programText_slice (code.of_external_eq m5) 0x190ca _ (by decide +kernel) (by decide +kernel)) e5.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x190ce (by decide)))
  change (shrR32Effect 0x1190ca 4 13 3 s5).Holds s5 s6 at e6
  have f6 : AgreesExcept [.reg 13,.flags,.rip] s5 s6 := e6.agrees
  have m6 := (f6.external (by simp [Component.Covers])).trans m5
  have v6 : s6.regValue .r13 = 0 := by
    have h : s6.regValue .r13 = ((s5.regValue .r13).setWidth 32 >>> 3).setWidth 64 := e6.writes
    rwa [v5] at h
  have ax6 : s6.regValue .rax = 32 :=
    ((((f3.trans f4).trans f5).trans f6).read (n := 64) (r := 0) (by simp)).trans ax2
  obtain ⟨t, a7, r7, e7⟩ :=
    (add_r32_r32_rex_effect_step 0x1190ce 0x41 0xc5 (by simp [RexNoWPrefix]) rfl).advances r6
      (programText_slice (code.of_external_eq m6) 0x190ce _ (by decide +kernel) (by decide +kernel)) e6.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x190d1 (by decide)))
  change (addR32R32Effect 0x1190ce 3 13 0 s6).Holds s6 t at e7
  have f7 : AgreesExcept [.reg 13,.flags,.rip] s6 t := e7.agrees
  refine ⟨t, a1.trans (a2.trans (a3.trans (a4.trans (a5.trans (a6.trans a7))))), r7, e7.rip, ?_, ?_⟩
  · have h : t.regValue .r13 = ((s6.regValue .r13).setWidth 32 + (s6.regValue .rax).setWidth 32).setWidth 64 := e7.writes
    rwa [v6, ax6] at h
  · exact ((((((f1.trans f2).trans f3).trans f4).trans f5).trans f6).trans f7).mono (by simp)

end P256.Proofs.ReadBe.Entry
