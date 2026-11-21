import P256.Spec
import P256.Proofs.Program.Arena
import P256.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Entry

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

theorem count_guard [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (hout : ¬ InProgram boundary.rip) (hip : s.RIP = 0x102398)
    (hcount : s.regValue .rsi = 2) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ t.RIP = 0x1023a1 ∧
      AgreesExcept [.flags, .rip] s t := by
  obtain ⟨u, hu, ru, eu⟩ :=
    (test_r64_r64_effect_step 0x102398 0x48 0xf6 (by simp [RexWPrefix]) rfl).advances
      ready (programText_slice (programLoaded_codeIn loaded) 0x2398 _
        (by decide) (by decide +kernel)) hip
      (boundary_ne_program hout (inProgram_of_textOffset 0x239b (by decide)))
  have fu : AgreesExcept [.flags, .rip] s u := eu.agrees
  have memu := fu.external (by simp [Component.Covers])
  have hz : (StatusFlags.ofRFLAGS u.RFLAGS).ZF = false := by
    have he := eu.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS u.RFLAGS).ZF = ((s.regValue .rsi &&& s.regValue .rsi) == 0) at he
    rw [hcount] at he
    exact he
  have hn : (jccEffect 0x10239b 6 4 ((0x78a : BitVec 32).signExtend 64) u).rip = 0x1023a1 := by
    simp [jccEffect, branchEffect, condHolds, hz]
  obtain ⟨t, ht, rt, et⟩ := (jcc_rel32_effect_step 0x10239b 4 0x78a).advances ru
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq memu)
      0x239b _ (by decide) (by decide +kernel)) ⟨eu.rip, by intro; decide⟩
    (by rw [hn]; exact boundary_ne_program hout (inProgram_of_textOffset 0x23a1 (by decide)))
  refine ⟨t, hu.trans ht, rt, et.rip.trans hn, ?_⟩
  exact (fu.trans et.agrees).mono (by simp [jccEffect])

theorem input_guard [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (hout : ¬ InProgram boundary.rip) (hip : s.RIP = 0x1023ad)
    (hptr : s.regValue .rax ≠ 0) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ t.RIP = 0x1023b6 ∧
      AgreesExcept [.flags, .rip] s t := by
  obtain ⟨a, ha, ra, ea⟩ :=
    (test_r64_r64_effect_step 0x1023ad 0x48 0xc0 (by simp [RexWPrefix]) rfl).advances
      ready (programText_slice (programLoaded_codeIn loaded) 0x23ad _
        (by decide) (by decide +kernel)) hip
      (boundary_ne_program hout (inProgram_of_textOffset 0x23b0 (by decide)))
  have fa : AgreesExcept [.flags, .rip] s a := ea.agrees
  have ma := fa.external (by simp [Component.Covers])
  have hz : (StatusFlags.ofRFLAGS a.RFLAGS).ZF = false := by
    have he := ea.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS a.RFLAGS).ZF = ((s.regValue .rax &&& s.regValue .rax) == 0) at he
    have hptr' : s.regValue .rax ≠ 0#64 := hptr
    have hz' : (s.regValue .rax == 0#64) = false := by
      exact beq_eq_false_iff_ne.mpr hptr'
    simp only [BitVec.and_self] at he
    exact he.trans hz'
  have hn : (jccEffect 0x1023b0 6 4 ((0x761 : BitVec 32).signExtend 64) a).rip = 0x1023b6 := by
    simp [jccEffect, branchEffect, condHolds, hz]
  obtain ⟨b, hb, rb, eb⟩ := (jcc_rel32_effect_step 0x1023b0 4 0x761).advances ra
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq ma)
      0x23b0 _ (by decide) (by decide +kernel)) ⟨ea.rip, by intro; decide⟩
    (by rw [hn]; exact boundary_ne_program hout (inProgram_of_textOffset 0x23b6 (by decide)))
  exact ⟨b, ha.trans hb, rb, eb.rip.trans hn,
    (fa.trans eb.agrees).mono (by simp [jccEffect])⟩

theorem length_guard [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (hout : ¬ InProgram boundary.rip) (hip : s.RIP = 0x1023b6)
    (hsize : s.regValue .rbp = 32) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ t.RIP = 0x1023c0 ∧
      AgreesExcept [.flags, .rip] s t := by
  obtain ⟨u, hu, ru, eu⟩ :=
    (cmp_r64_imm8_effect_step 0x1023b6 0x48 0xfd 32 (by simp [RexWPrefix]) rfl rfl).advances
      ready (programText_slice (programLoaded_codeIn loaded) 0x23b6 _
        (by decide) (by decide +kernel)) hip
      (boundary_ne_program hout (inProgram_of_textOffset 0x23ba (by decide)))
  have fu : AgreesExcept [.flags, .rip] s u := eu.agrees
  have memu := fu.external (by simp [Component.Covers])
  have hz : (StatusFlags.ofRFLAGS u.RFLAGS).ZF = true := by
    have he := eu.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS u.RFLAGS).ZF = ((s.regValue .rbp - 32) == 0) at he
    rw [hsize] at he
    exact he
  have hn : (jccEffect 0x1023ba 6 5 ((0x76b : BitVec 32).signExtend 64) u).rip = 0x1023c0 := by
    simp [jccEffect, branchEffect, condHolds, hz]
  obtain ⟨t, ht, rt, et⟩ := (jcc_rel32_effect_step 0x1023ba 5 0x76b).advances ru
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq memu)
      0x23ba _ (by decide) (by decide +kernel)) ⟨eu.rip, by intro; decide⟩
    (by rw [hn]; exact boundary_ne_program hout (inProgram_of_textOffset 0x23c0 (by decide)))
  refine ⟨t, hu.trans ht, rt, et.rip.trans hn, ?_⟩
  exact (fu.trans et.agrees).mono (by simp [jccEffect])

end P256.Proofs.Signing.Wrapper.Entry
