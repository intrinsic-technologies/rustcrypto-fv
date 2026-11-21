import X86Proofs.Instructions.Mov.Triple
import P256.Proofs.Program.Code
import P256.Proofs.ReadBe.Interface
import P256.Proofs.Common.Field.SquareRoot.Exponent.Multiply.Shift
import P256.Proofs.Common.Encoding.Serialize.Tail.Prepare.Encode.Immediate
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field.SquareRoot.ExponentMultiply (shlR32Effect shl_r32_imm8_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice)

namespace P256.Proofs.ReadBe.Entry

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem capacity_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (rip : s.RIP = 0x11909e)
    (limbs : s.regValue .rcx = 4) (bits : s.regValue .r8 = 256)
    (outside : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 6 s t ∧ ReadyToStep t ∧ t.RIP = 0x1190b1 ∧
      t.regValue .r14 = s.regValue .rdx ∧
      AgreesExcept [.reg 0,.reg 2,.reg 14,.flags,.rip] s t := by
  have code := programLoaded_codeIn loaded
  obtain ⟨s1, a1, r1, e1⟩ :=
    (mov_r64_r64_effect_step 0x11909e 0x49 0xd6 (by simp [RexWPrefix]) rfl).advances ready
      (programText_slice code 0x1909e _ (by decide +kernel) (by decide +kernel)) rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x190a1 (by decide)))
  change (movR64R64Effect 0x11909e 14 2 s).Holds s s1 at e1
  have f1 : AgreesExcept [.reg 14,.rip] s s1 := e1.agrees
  have m1 := f1.external (by simp [Component.Covers])
  have cx1 : s1.regValue .rcx = 4 :=
    (f1.read (n := 64) (r := 1) (by simp)).trans limbs
  obtain ⟨s2, a2, r2, e2⟩ :=
    (mov_r32_r32_effect_step 0x1190a1 0xca rfl).advances r1
      (programText_slice (code.of_external_eq m1) 0x190a1 _ (by decide +kernel) (by decide +kernel)) e1.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x190a3 (by decide)))
  change (movR32R32Effect 0x1190a1 2 2 1 s1).Holds s1 s2 at e2
  have f2 : AgreesExcept [.reg 2,.rip] s1 s2 := e2.agrees
  have m2 := (f2.external (by simp [Component.Covers])).trans m1
  have dx2 : s2.regValue .rdx = 4 := by
    have h : s2.regValue .rdx = ((s1.regValue .rcx).setWidth 32).setWidth 64 := e2.writes
    rwa [cx1] at h
  obtain ⟨s3, a3, r3, e3⟩ :=
    (shl_r32_imm8_effect_step 0x1190a3 0xe2 6 rfl rfl).advances r2
      (programText_slice (code.of_external_eq m2) 0x190a3 _ (by decide +kernel) (by decide +kernel)) e2.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x190a6 (by decide)))
  change (shlR32Effect 0x1190a3 3 2 6 s2).Holds s2 s3 at e3
  have f3 : AgreesExcept [.reg 2,.flags,.rip] s2 s3 := e3.agrees
  have m3 := (f3.external (by simp [Component.Covers])).trans m2
  have dx3 : s3.regValue .rdx = 256 := by
    have h : s3.regValue .rdx = ((s2.regValue .rdx).setWidth 32 <<< 6).setWidth 64 := e3.writes
    rwa [dx2] at h
  obtain ⟨s4, a4, r4, e4⟩ :=
    (P256.Proofs.Common.Encoding.Serialize.prepare_mov_al_imm8_effect_step 0x1190a6 3).advances r3
      (programText_slice (code.of_external_eq m3) 0x190a6 _ (by decide +kernel) (by decide +kernel)) e3.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x190a8 (by decide)))
  have f4 : AgreesExcept [.reg 0,.rip] s3 s4 := e4.agrees
  have m4 := (f4.external (by simp [Component.Covers])).trans m3
  have dx4 : s4.regValue .rdx = 256 := (f4.read (n := 64) (r := 2) (by simp)).trans dx3
  have r84 : s4.regValue .r8 = 256 :=
    ((((f1.trans f2).trans f3).trans f4).read (n := 64) (r := 8) (by simp)).trans bits
  obtain ⟨s5, a5, r5, e5⟩ :=
    (cmp_r32_r32_rex_effect_step 0x1190a8 0x44 0xc2 (by simp [RexNoWPrefix]) rfl).advances r4
      (programText_slice (code.of_external_eq m4) 0x190a8 _ (by decide +kernel) (by decide +kernel)) e4.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x190ab (by decide)))
  change (cmpR32R32Effect 0x1190a8 3 2 8 s4).Holds s4 s5 at e5
  have f5 : AgreesExcept [.flags,.rip] s4 s5 := e5.agrees
  have m5 := (f5.external (by simp [Component.Covers])).trans m4
  have cf : (StatusFlags.ofRFLAGS s5.RFLAGS).CF = false := by
    have h := e5.flags.1
    change (StatusFlags.ofRFLAGS s5.RFLAGS).CF =
      (cmpSpec ((s4.regValue .rdx).setWidth 32) ((s4.regValue .r8).setWidth 32)).CF at h
    rw [dx4, r84] at h
    exact h
  obtain ⟨t, step, rt, raw⟩ := jcc_rel32_effect_step 0x1190ab 2 0xe5 s5 r5
    (programText_slice (code.of_external_eq m5) 0x190ab _ (by decide +kernel) (by decide +kernel))
    ⟨e5.rip, by intro _; decide +kernel⟩
  have et := jccEffect_not_taken (show condHolds 2 (StatusFlags.ofRFLAGS s5.RFLAGS) = false from cf) raw
  have advanceT : Advances boundary 1 s5 t := Advances.of_step step (.inl (by
    rw [et.rip]
    exact boundary_ne_program outside (inProgram_of_textOffset 0x190b1 (by decide))))
  have ft : AgreesExcept [.rip] s5 t := et.agrees
  refine ⟨t, a1.trans (a2.trans (a3.trans (a4.trans (a5.trans advanceT)))), rt, et.rip, ?_, ?_⟩
  · exact (((((f2.trans f3).trans f4).trans f5).trans ft).read (n := 64) (r := 14) (by simp)).trans e1.writes
  · exact (((((f1.trans f2).trans f3).trans f4).trans f5).trans ft).mono (by simp)

end P256.Proofs.ReadBe.Entry
