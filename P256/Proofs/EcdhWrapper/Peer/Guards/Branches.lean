import P256.Spec
import P256.Proofs.Program.Arena
import P256.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Peer.Guards

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

theorem count_guard [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (hout : ¬ InProgram boundary.rip) (hip : s.RIP = 0x1069b6)
    (hcount : s.regValue .r13 = 2) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ t.RIP = 0x1069c0 ∧
      AgreesExcept [.flags, .rip] s t := by
  obtain ⟨u, hu, ru, eu⟩ :=
    (cmp_r64_imm8_effect_step 0x1069b6 0x49 0xfd 1 (by simp [RexWPrefix]) rfl rfl).advances
      ready (programText_slice (programLoaded_codeIn loaded) 0x69b6 _
        (by decide) (by decide +kernel)) hip
      (boundary_ne_program hout (inProgram_of_textOffset 0x69ba (by decide)))
  have fu : AgreesExcept [.flags, .rip] s u := eu.agrees
  have memu := fu.external (by simp [Component.Covers])
  have hz : (StatusFlags.ofRFLAGS u.RFLAGS).ZF = false := by
    have he := eu.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS u.RFLAGS).ZF = ((s.regValue .r13 - 1) == 0) at he
    rw [hcount] at he
    exact he
  have hn : (jccEffect 0x1069ba 6 4 ((0x32e : BitVec 32).signExtend 64) u).rip = 0x1069c0 := by
    simp [jccEffect, branchEffect, condHolds, hz]
  obtain ⟨t, ht, rt, et⟩ := (jcc_rel32_effect_step 0x1069ba 4 0x32e).advances ru
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq memu)
      0x69ba _ (by decide) (by decide +kernel)) ⟨eu.rip, by intro; decide⟩
    (by rw [hn]; exact boundary_ne_program hout (inProgram_of_textOffset 0x69c0 (by decide)))
  refine ⟨t, hu.trans ht, rt, et.rip.trans hn, ?_⟩
  exact (fu.trans et.agrees).mono (by simp [jccEffect])

theorem pointer_guard [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (hout : ¬ InProgram boundary.rip) (hip : s.RIP = 0x1069c9)
    (hptr : s.regValue .r12 ≠ 0) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ t.RIP = 0x1069d2 ∧
      AgreesExcept [.flags, .rip] s t := by
  obtain ⟨a, ha, ra, ea⟩ :=
    (test_r64_r64_effect_step 0x1069c9 0x4d 0xe4 (by simp [RexWPrefix]) rfl).advances
      ready (programText_slice (programLoaded_codeIn loaded) 0x69c9 _
        (by decide) (by decide +kernel)) hip
      (boundary_ne_program hout (inProgram_of_textOffset 0x69cc (by decide)))
  have fa : AgreesExcept [.flags, .rip] s a := ea.agrees
  have ma := fa.external (by simp [Component.Covers])
  have hz : (StatusFlags.ofRFLAGS a.RFLAGS).ZF = false := by
    have he := ea.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS a.RFLAGS).ZF = ((s.regValue .r12 &&& s.regValue .r12) == 0) at he
    have hptr' : s.regValue .r12 ≠ 0#64 := hptr
    have hz' : (s.regValue .r12 == 0#64) = false := by
      exact beq_eq_false_iff_ne.mpr hptr'
    simp only [BitVec.and_self] at he
    exact he.trans hz'
  have hn : (jccEffect 0x1069cc 6 4 ((0x2e7 : BitVec 32).signExtend 64) a).rip = 0x1069d2 := by
    simp [jccEffect, branchEffect, condHolds, hz]
  obtain ⟨b, hb, rb, eb⟩ := (jcc_rel32_effect_step 0x1069cc 4 0x2e7).advances ra
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq ma)
      0x69cc _ (by decide) (by decide +kernel)) ⟨ea.rip, by intro; decide⟩
    (by rw [hn]; exact boundary_ne_program hout (inProgram_of_textOffset 0x69d2 (by decide)))
  exact ⟨b, ha.trans hb, rb, eb.rip.trans hn,
    (fa.trans eb.agrees).mono (by simp [jccEffect])⟩

theorem nonempty_guard [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (hout : ¬ InProgram boundary.rip) (hip : s.RIP = 0x1069d2)
    (hptr : s.regValue .rbp ≠ 0) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ t.RIP = 0x1069db ∧
      AgreesExcept [.flags, .rip] s t := by
  obtain ⟨a, ha, ra, ea⟩ :=
    (test_r64_r64_effect_step 0x1069d2 0x48 0xed (by simp [RexWPrefix]) rfl).advances
      ready (programText_slice (programLoaded_codeIn loaded) 0x69d2 _
        (by decide) (by decide +kernel)) hip
      (boundary_ne_program hout (inProgram_of_textOffset 0x69d5 (by decide)))
  have fa : AgreesExcept [.flags, .rip] s a := ea.agrees
  have ma := fa.external (by simp [Component.Covers])
  have hz : (StatusFlags.ofRFLAGS a.RFLAGS).ZF = false := by
    have he := ea.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS a.RFLAGS).ZF = ((s.regValue .rbp &&& s.regValue .rbp) == 0) at he
    have hptr' : s.regValue .rbp ≠ 0#64 := hptr
    have hz' : (s.regValue .rbp == 0#64) = false := by
      exact beq_eq_false_iff_ne.mpr hptr'
    simp only [BitVec.and_self] at he
    exact he.trans hz'
  have hn : (jccEffect 0x1069d5 6 4 ((0x313 : BitVec 32).signExtend 64) a).rip = 0x1069db := by
    simp [jccEffect, branchEffect, condHolds, hz]
  obtain ⟨b, hb, rb, eb⟩ := (jcc_rel32_effect_step 0x1069d5 4 0x313).advances ra
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq ma)
      0x69d5 _ (by decide) (by decide +kernel)) ⟨ea.rip, by intro; decide⟩
    (by rw [hn]; exact boundary_ne_program hout (inProgram_of_textOffset 0x69db (by decide)))
  exact ⟨b, ha.trans hb, rb, eb.rip.trans hn,
    (fa.trans eb.agrees).mono (by simp [jccEffect])⟩

end P256.Proofs.EcdhWrapper.Peer.Guards
