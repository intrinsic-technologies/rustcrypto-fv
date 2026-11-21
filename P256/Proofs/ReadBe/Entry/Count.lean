import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Program.Code
import P256.Proofs.Common.Memory.Copy.RegisterOps.Cmov
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.MovLoad.Triple

set_option autoImplicit false

open P256.Proofs.Common.Instructions (cmovR64R64Effect cmov_r64_r64_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice)

namespace P256.Proofs.ReadBe.Entry

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem count_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (rip : s.RIP = 0x1190e1)
    (size : s.regValue .r13 = 32) (readable : MemReadable s (stackPtr s + 8) 8)
    (value : memLoad s.external (stackPtr s + 8) 64 = 4)
    (outside : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 7 s t ∧ ReadyToStep t ∧ t.RIP = 0x1190fa ∧
      t.regValue .rbp = 4 ∧ AgreesExcept [.reg 0,.reg 5,.flags,.rip] s t := by
  have code := programLoaded_codeIn loaded
  obtain ⟨s1, a1, r1, e1⟩ :=
    (lea_r64_effect_step 0x1190e1 0x49 (by simp [RexWPrefix]) 5
      (.base 13 (.d8 7)) (by decide +kernel) rfl rfl).advances ready
      (programText_slice code 0x190e1 _ (by decide +kernel) (by decide +kernel)) rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x190e5 (by decide)))
  have f1 : AgreesExcept [.reg 5,.rip] s s1 := e1.agrees
  have m1 := f1.external (by simp [Component.Covers])
  have bp1 : s1.regValue .rbp = 39 := by
    have h : s1.regValue .rbp = s.regValue .r13 + 7 := e1.writes
    rwa [size] at h
  obtain ⟨s2, a2, r2, e2⟩ :=
    (shr_r64_imm8_effect_step 0x1190e5 0x48 0xed 3 (by simp [RexWPrefix]) rfl rfl).advances r1
      (programText_slice (code.of_external_eq m1) 0x190e5 _ (by decide +kernel) (by decide +kernel)) e1.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x190e9 (by decide)))
  change (shrR64Effect 0x1190e5 4 5 3 s1).Holds s1 s2 at e2
  have f2 : AgreesExcept [.reg 5,.flags,.rip] s1 s2 := e2.agrees
  have m2 := (f2.external (by simp [Component.Covers])).trans m1
  have bp2 : s2.regValue .rbp = 4 := by
    have h : s2.regValue .rbp = s1.regValue .rbp >>> 3 := e2.writes
    rwa [bp1] at h
  have sp2 : stackPtr s2 = stackPtr s := (f1.trans f2).read (n := 64) (r := 4) (by simp)
  obtain ⟨s3, a3, r3, e3⟩ :=
    (mov_r64_m64_effect_step 0x1190e9 0x48 (by simp [RexWPrefix]) 0
      (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl).advances r2
      (programText_slice (code.of_external_eq m2) 0x190e9 _ (by decide +kernel) (by decide +kernel))
      ⟨e2.rip, by
        change MemReadable s2 (stackPtr s2 + 8) 8
        rw [sp2]
        exact readable.of_external_eq m2⟩
      (boundary_ne_program outside (inProgram_of_textOffset 0x190ee (by decide)))
  have f3 : AgreesExcept [.reg 0,.rip] s2 s3 := e3.agrees
  have m3 := (f3.external (by simp [Component.Covers])).trans m2
  have ax3 : s3.regValue .rax = 4 := by
    have h : s3.regValue .rax = memLoad s2.external (stackPtr s2 + 8) 64 := e3.writes
    rwa [m2, sp2, value] at h
  have bp3 : s3.regValue .rbp = 4 := (f3.read (n := 64) (r := 5) (by simp)).trans bp2
  obtain ⟨s4, a4, r4, e4⟩ :=
    (cmp_r64_r64_effect_step 0x1190ee 0x48 0xe8 (by simp [RexWPrefix]) rfl).advances r3
      (programText_slice (code.of_external_eq m3) 0x190ee _ (by decide +kernel) (by decide +kernel)) e3.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x190f1 (by decide)))
  change (cmpR64R64Effect 0x1190ee 0 5 s3).Holds s3 s4 at e4
  have f4 : AgreesExcept [.flags,.rip] s3 s4 := e4.agrees
  have m4 := (f4.external (by simp [Component.Covers])).trans m3
  have cf : (StatusFlags.ofRFLAGS s4.RFLAGS).CF = false := by
    have h := e4.flags.1
    change (StatusFlags.ofRFLAGS s4.RFLAGS).CF = (cmpSpec (s3.regValue .rax) (s3.regValue .rbp)).CF at h
    rw [ax3, bp3] at h
    exact h
  have bp4 : s4.regValue .rbp = 4 := (f4.read (n := 64) (r := 5) (by simp)).trans bp3
  obtain ⟨s5, a5, r5, e5⟩ :=
    (cmov_r64_r64_effect_step 0x1190f1 0x48 0x42 0xe8 (by simp [RexWPrefix]) (.inl rfl) rfl).advances r4
      (programText_slice (code.of_external_eq m4) 0x190f1 _ (by decide +kernel) (by decide +kernel)) e4.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x190f5 (by decide)))
  change (cmovR64R64Effect 0x1190f1 2 5 0 s4).Holds s4 s5 at e5
  have f5 : AgreesExcept [.reg 5,.rip] s4 s5 := e5.agrees
  have m5 := (f5.external (by simp [Component.Covers])).trans m4
  have bp5 : s5.regValue .rbp = 4 := by
    have h : s5.regValue .rbp = if (StatusFlags.ofRFLAGS s4.RFLAGS).CF then s4.regValue .rax else s4.regValue .rbp := e5.writes
    simpa only [cf, Bool.false_eq_true, ↓reduceIte, bp4] using h
  obtain ⟨s6, a6, r6, e6⟩ :=
    (test_r64_r64_effect_step 0x1190f5 0x48 0xed (by simp [RexWPrefix]) rfl).advances r5
      (programText_slice (code.of_external_eq m5) 0x190f5 _ (by decide +kernel) (by decide +kernel)) e5.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x190f8 (by decide)))
  change (testR64R64Effect 0x1190f5 5 5 s5).Holds s5 s6 at e6
  have f6 : AgreesExcept [.flags,.rip] s5 s6 := e6.agrees
  have m6 := (f6.external (by simp [Component.Covers])).trans m5
  have zf : (StatusFlags.ofRFLAGS s6.RFLAGS).ZF = false := by
    have h := e6.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS s6.RFLAGS).ZF = ((s5.regValue .rbp &&& s5.regValue .rbp) == 0) at h
    rw [bp5] at h
    exact h
  obtain ⟨t, step, rt, raw⟩ := jcc_rel8_effect_step 0x1190f8 4 0x76 s6 r6
    (programText_slice (code.of_external_eq m6) 0x190f8 _ (by decide +kernel) (by decide +kernel))
    ⟨e6.rip, by intro _; decide +kernel⟩
  have et := jccEffect_not_taken (show condHolds 4 (StatusFlags.ofRFLAGS s6.RFLAGS) = false from zf) raw
  have advanceT : Advances boundary 1 s6 t := Advances.of_step step (.inl (by
    rw [et.rip]
    exact boundary_ne_program outside (inProgram_of_textOffset 0x190fa (by decide))))
  have ft : AgreesExcept [.rip] s6 t := et.agrees
  refine ⟨t, a1.trans (a2.trans (a3.trans (a4.trans (a5.trans (a6.trans advanceT))))), rt, et.rip, ?_, ?_⟩
  · exact ((f6.trans ft).read (n := 64) (r := 5) (by simp)).trans bp5
  · exact ((((((f1.trans f2).trans f3).trans f4).trans f5).trans f6).trans ft).mono (by simp)

end P256.Proofs.ReadBe.Entry
