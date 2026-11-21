import P256.Proofs.Program.Code
import X86Proofs.Instructions.Test.Generated.RR.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decode

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem length_branch [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (outside : ¬ InProgram boundary.rip) (rip : s.RIP = 0x10e4ee) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧
      t.RIP = (if s.regValue .rdx = 0 then 0x10e68e else 0x10e4f7) ∧
      AgreesExcept [.flags, .rip] s t := by
  obtain ⟨u, hu, ru, eu⟩ :=
    (test_r64_r64_effect_step 0x10e4ee 0x48 0xd2 (by simp [RexWPrefix]) rfl).advances
      ready (programText_slice (programLoaded_codeIn loaded) 0xe4ee _
        (by decide) (by decide +kernel)) rip
      (boundary_ne_program outside (inProgram_of_textOffset 0xe4f1 (by decide)))
  have fu : AgreesExcept [.flags, .rip] s u := eu.agrees
  have memu := fu.external (by simp [Component.Covers])
  have hz : (StatusFlags.ofRFLAGS u.RFLAGS).ZF = (s.regValue .rdx == 0) := by
    have he := eu.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS u.RFLAGS).ZF = ((s.regValue .rdx &&& s.regValue .rdx) == 0) at he
    simpa only [BitVec.and_self] using he
  have hn : (jccEffect 0x10e4f1 6 4 ((0x197 : BitVec 32).signExtend 64) u).rip =
      if s.regValue .rdx = 0 then 0x10e68e else 0x10e4f7 := by
    simp [jccEffect, branchEffect, branchTarget, condHolds, hz]
  obtain ⟨t, ht, rt, et⟩ := (jcc_rel32_effect_step 0x10e4f1 4 0x197).advances ru
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq memu)
      0xe4f1 _ (by decide) (by decide +kernel)) ⟨eu.rip, by intro; decide⟩
    (by rw [hn]; split
        · exact boundary_ne_program outside (inProgram_of_textOffset 0xe68e (by decide))
        · exact boundary_ne_program outside (inProgram_of_textOffset 0xe4f7 (by decide)))
  refine ⟨t, hu.trans ht, rt, et.rip.trans hn, ?_⟩
  exact (fu.trans et.agrees).mono (by simp [jccEffect])

end P256.Proofs.Sec1.Decode
