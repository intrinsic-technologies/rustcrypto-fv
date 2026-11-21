import P256.Proofs.Program.Code
import X86Proofs.Instructions.Test.Generated.RR.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.ExponentInitialize

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem bits_guard [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (hout : ¬ InProgram boundary.rip) (hip : s.RIP = 0x114c12)
    (hcount : (Operand.reg 1 : Operand 32).read s = 254) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ t.RIP = 0x114c1a ∧
      AgreesExcept [.flags, .rip] s t := by
  obtain ⟨u, hu, ru, eu⟩ :=
    (test_r32_r32_effect_step 0x114c12 0xc9 rfl).advances
      ready (programText_slice (programLoaded_codeIn loaded) 0x14c12 _
        (by decide) (by decide +kernel)) hip
      (boundary_ne_program hout (inProgram_of_textOffset 0x14c14 (by decide)))
  have fu : AgreesExcept [.flags, .rip] s u := eu.agrees
  have memu := fu.external (by simp [Component.Covers])
  have hz : (StatusFlags.ofRFLAGS u.RFLAGS).ZF = false := by
    have he := eu.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS u.RFLAGS).ZF = (((Operand.reg 1 : Operand 32).read s &&& (Operand.reg 1 : Operand 32).read s) == 0) at he
    rw [hcount] at he
    exact he
  have hn : (jccEffect 0x114c14 6 4 ((0xd12 : BitVec 32).signExtend 64) u).rip = 0x114c1a := by
    simp [jccEffect, branchEffect, condHolds, hz]
  obtain ⟨t, ht, rt, et⟩ := (jcc_rel32_effect_step 0x114c14 4 0xd12).advances ru
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq memu)
      0x14c14 _ (by decide) (by decide +kernel)) ⟨eu.rip, by intro; decide⟩
    (by rw [hn]; exact boundary_ne_program hout (inProgram_of_textOffset 0x14c1a (by decide)))
  refine ⟨t, hu.trans ht, rt, et.rip.trans hn, ?_⟩
  exact (fu.trans et.agrees).mono (by simp [jccEffect])

end P256.Proofs.Sec1.SquareRoot.ExponentInitialize
