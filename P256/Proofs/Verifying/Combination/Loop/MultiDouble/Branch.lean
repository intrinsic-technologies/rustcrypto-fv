import P256.Proofs.Verifying.Combination.Loop.MultiRoundState
import X86Proofs.Instructions.Test.Generated.R8Imm8.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice readyToStep)

namespace P256.Proofs.Verifying.Combination.Loop.Multi

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Projective P256.Proofs.Program

theorem double_branch [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64} {p q : Projective} {u v : Nat}
    (pre : MultiPre s boundary tables digits) (state : Memory s t tables digits p q u v) (rip : t.RIP = 0x10f174) :
    ∃ w, Advances boundary 2 t w ∧ Memory s w tables digits p q u v ∧
      w.RIP = (if (t.regValue .r14).getLsbD 0 then 0x10f17a else 0x10f1a3) ∧
      AgreesExcept [.flags, .rip] t w := by
  obtain ⟨a, runA, readyA, effectA⟩ :=
    (test_r8_imm8_effect_step 0x10f174 0x41 0xc6 1 (by simp [RexPrefix]) rfl rfl).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0xf174 [0x41, 0xf6, 0xc6, 0x01]
        (by decide) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf178 (by decide)))
  have frameA : AgreesExcept [.flags, .rip] t a := effectA.agrees
  have stateA := state.after_registers readyA frameA (by simp [Component.Covers]) (by simp)
  have zf : (StatusFlags.ofRFLAGS a.RFLAGS).ZF = !(t.regValue .r14).getLsbD 0 := by
    have h := effectA.flags.2.2.2.1
    change _ = ((t.regValue .r14).extractLsb' 0 8 &&& 1#8 == 0#8) at h
    rw [BitVec.and_one_eq_setWidth_ofBool_getLsbD] at h
    rw [BitVec.getLsbD_extractLsb'] at h
    change _ = ((BitVec.ofBool ((t.regValue .r14).getLsbD 0)).setWidth 8 == 0#8) at h
    cases he : (t.regValue .r14).getLsbD 0 <;> rw [he] at h <;> exact h
  have next : (jccEffect 0x10f178 2 4 ((0x29 : BitVec 8).signExtend 64) a).rip =
      (if (t.regValue .r14).getLsbD 0 then 0x10f17a else 0x10f1a3) := by
    cases he : (t.regValue .r14).getLsbD 0 <;>
      simp only [jccEffect, branchEffect, condHolds, zf, he] <;> rfl
  obtain ⟨w, runW, readyW, effectW⟩ :=
    (jcc_rel8_effect_step 0x10f178 4 0x29).advances readyA
      (programText_slice (programLoaded_codeIn stateA.loaded) 0xf178 [0x74, 0x29]
        (by decide) (by decide +kernel))
      ⟨effectA.rip, by intro h; decide +kernel⟩
      (by rw [next]; split
          · exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf17a (by decide))
          · exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf1a3 (by decide)))
  have frameW : AgreesExcept [.rip] a w := effectW.agrees
  have frame : AgreesExcept [.flags, .rip] t w := (frameA.trans frameW).mono (by simp)
  exact ⟨w, runA.trans runW, state.after_registers readyW frame (by simp [Component.Covers])
    (by simp), effectW.rip.trans next, frame⟩

end P256.Proofs.Verifying.Combination.Loop.Multi
