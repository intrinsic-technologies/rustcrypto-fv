import P256.Proofs.Verifying.Core.Interface
import P256.Proofs.Program.Code
import P256.Proofs.Common.Field.Operations.Select.TestAl
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Output

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem branch [Bindings] {t : RamState} {boundary : ReturnBoundary} {accepted : Bool}
    (ready : ReadyToStep t) (loaded : ProgramLoaded t)
    (outside : ¬ InProgram boundary.rip) (rip : t.RIP = 0x10e16c)
    (rax : (t.regValue .rax).setWidth 8 = if accepted then 1 else 0) :
    ∃ u, Advances boundary 2 t u ∧ ReadyToStep u ∧
      u.RIP = (if accepted then 0x10e170 else 0x10e17c) ∧
      AgreesExcept [.flags, .rip] t u := by
  obtain ⟨a, ha, ra, ea⟩ := (P256.Proofs.Common.Field.test_al_al_effect_step 0x10e16c).advances
    ready (programText_slice (programLoaded_codeIn loaded) 0xe16c _
      (by decide) (by decide +kernel)) rip
    (boundary_ne_program outside (inProgram_of_textOffset 0xe16e (by decide)))
  have fa : AgreesExcept [.flags, .rip] t a := ea.agrees
  have ma := fa.external (by simp [Component.Covers])
  have zf : (StatusFlags.ofRFLAGS a.RFLAGS).ZF = !accepted := by
    have hz := ea.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS a.RFLAGS).ZF = ((t.regValue .rax).setWidth 8 == 0) at hz
    rw [hz, rax]
    cases accepted <;> decide +kernel
  have cond : condHolds 4 (StatusFlags.ofRFLAGS a.RFLAGS) = !accepted := zf
  have next : (jccEffect 0x10e16e 2 4 ((12 : BitVec 8).signExtend 64) a).rip =
      if accepted then 0x10e170 else 0x10e17c := by
    simp only [jccEffect, cond]
    cases accepted <;> rfl
  obtain ⟨u, hu, ru, eu⟩ := (jcc_rel8_effect_step 0x10e16e 4 12).advances ra
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq ma) 0xe16e _
      (by decide) (by decide +kernel)) ⟨ea.rip, by intro; decide⟩
    (by rw [next]; cases accepted
        · exact boundary_ne_program outside (inProgram_of_textOffset 0xe17c (by decide))
        · exact boundary_ne_program outside (inProgram_of_textOffset 0xe170 (by decide)))
  have fu : AgreesExcept [.rip] a u := eu.agrees
  exact ⟨u, ha.trans hu, ru, eu.rip.trans next, (fa.trans fu).mono (by simp)⟩

end P256.Proofs.Verifying.Core.Output
