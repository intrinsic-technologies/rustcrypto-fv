import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Program.Code
import P256.Proofs.Common.Memory.Copy.RegisterOps.Cmov
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple

set_option autoImplicit false

open P256.Proofs.Common.Instructions (cmovR64R64Effect cmov_r64_r64_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice)

namespace P256.Proofs.ReadBe.Entry

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem clamp_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (rip : s.RIP = 0x1190d1)
    (count : s.regValue .rsi = 32) (size : s.regValue .r13 = 32)
    (outside : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 4 s t ∧ ReadyToStep t ∧ t.RIP = 0x1190e1 ∧
      t.regValue .r13 = 32 ∧ AgreesExcept [.reg 13,.flags,.rip] s t := by
  have code := programLoaded_codeIn loaded
  obtain ⟨s1, a1, r1, e1⟩ :=
    (cmp_r64_r64_effect_step 0x1190d1 0x4c 0xee (by simp [RexWPrefix]) rfl).advances ready
      (programText_slice code 0x190d1 _ (by decide +kernel) (by decide +kernel)) rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x190d4 (by decide)))
  change (cmpR64R64Effect 0x1190d1 6 13 s).Holds s s1 at e1
  have f1 : AgreesExcept [.flags,.rip] s s1 := e1.agrees
  have m1 := f1.external (by simp [Component.Covers])
  have cf : (StatusFlags.ofRFLAGS s1.RFLAGS).CF = false := by
    have h := e1.flags.1
    change (StatusFlags.ofRFLAGS s1.RFLAGS).CF = (cmpSpec (s.regValue .rsi) (s.regValue .r13)).CF at h
    rw [count, size] at h
    exact h
  have size1 : s1.regValue .r13 = 32 := (f1.read (n := 64) (r := 13) (by simp)).trans size
  obtain ⟨s2, a2, r2, e2⟩ :=
    (cmov_r64_r64_effect_step 0x1190d4 0x4c 0x42 0xee (by simp [RexWPrefix]) (.inl rfl) rfl).advances r1
      (programText_slice (code.of_external_eq m1) 0x190d4 _ (by decide +kernel) (by decide +kernel)) e1.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x190d8 (by decide)))
  change (cmovR64R64Effect 0x1190d4 2 13 6 s1).Holds s1 s2 at e2
  have f2 : AgreesExcept [.reg 13,.rip] s1 s2 := e2.agrees
  have m2 := (f2.external (by simp [Component.Covers])).trans m1
  have size2 : s2.regValue .r13 = 32 := by
    have h : s2.regValue .r13 = if (StatusFlags.ofRFLAGS s1.RFLAGS).CF then s1.regValue .rsi else s1.regValue .r13 := e2.writes
    simpa only [cf, Bool.false_eq_true, ↓reduceIte, size1] using h
  obtain ⟨s3, a3, r3, e3⟩ :=
    (test_r64_r64_effect_step 0x1190d8 0x4d 0xed (by simp [RexWPrefix]) rfl).advances r2
      (programText_slice (code.of_external_eq m2) 0x190d8 _ (by decide +kernel) (by decide +kernel)) e2.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x190db (by decide)))
  change (testR64R64Effect 0x1190d8 13 13 s2).Holds s2 s3 at e3
  have f3 : AgreesExcept [.flags,.rip] s2 s3 := e3.agrees
  have m3 := (f3.external (by simp [Component.Covers])).trans m2
  have zf : (StatusFlags.ofRFLAGS s3.RFLAGS).ZF = false := by
    have h := e3.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS s3.RFLAGS).ZF = ((s2.regValue .r13 &&& s2.regValue .r13) == 0) at h
    rw [size2] at h
    exact h
  obtain ⟨t, step, rt, raw⟩ := jcc_rel32_effect_step 0x1190db 4 0x8f s3 r3
    (programText_slice (code.of_external_eq m3) 0x190db _ (by decide +kernel) (by decide +kernel))
    ⟨e3.rip, by intro _; decide +kernel⟩
  have et := jccEffect_not_taken (show condHolds 4 (StatusFlags.ofRFLAGS s3.RFLAGS) = false from zf) raw
  have advanceT : Advances boundary 1 s3 t := Advances.of_step step (.inl (by
    rw [et.rip]
    exact boundary_ne_program outside (inProgram_of_textOffset 0x190e1 (by decide))))
  have ft : AgreesExcept [.rip] s3 t := et.agrees
  refine ⟨t, a1.trans (a2.trans (a3.trans advanceT)), rt, et.rip, ?_, ?_⟩
  · exact ((f3.trans ft).read (n := 64) (r := 13) (by simp)).trans size2
  · exact (((f1.trans f2).trans f3).trans ft).mono (by simp)

end P256.Proofs.ReadBe.Entry
