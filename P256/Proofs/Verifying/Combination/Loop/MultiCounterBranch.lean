import P256.Proofs.Verifying.Combination.Loop.MultiPrologue
import X86Proofs.Instructions.Test.Generated.RR.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice readyToStep)

namespace P256.Proofs.Verifying.Combination.Loop.Multi

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Projective P256.Proofs.Program P256.Proofs.Program.ScalarFrame

theorem countdown_branch [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64} {k : Nat}
    (pre : MultiPre s boundary tables digits) (state : State s t)
    (rip : t.RIP = 0x10f16b) (count : t.regValue .rbx = BitVec.ofNat 64 k) (bound : k ≤ 257) :
    ∃ w, Advances boundary 2 t w ∧ State s w ∧
      w.RIP = (if k = 0 then 0x10f301 else 0x10f174) ∧
      AgreesExcept [.flags, .rip] t w := by
  obtain ⟨a, runA, readyA, effectA⟩ :=
    (test_r64_r64_effect_step 0x10f16b 0x48 0xdb (by simp [RexWPrefix]) rfl).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0xf16b [0x48, 0x85, 0xdb]
        (by decide) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf16e (by decide)))
  have frameA : AgreesExcept [.flags, .rip] t a := effectA.agrees
  have stateA := state.after_registers readyA frameA (by simp [Component.Covers]) (by simp)
  have zf : (StatusFlags.ofRFLAGS a.RFLAGS).ZF = decide (k = 0) := by
    have h := effectA.flags.2.2.2.1
    change _ = (t.regValue .rbx &&& t.regValue .rbx == 0#64) at h
    rw [BitVec.and_self, count] at h
    exact h.trans ((show ∀ i : Fin 258, (BitVec.ofNat 64 i.val == 0#64) = decide (i.val = 0)
      by decide +kernel) ⟨k, by omega⟩)
  have next : (jccEffect 0x10f16e 6 4 ((0x18d : BitVec 32).signExtend 64) a).rip =
      (if k = 0 then 0x10f301 else 0x10f174) := by
    by_cases h : k = 0 <;> simp [jccEffect, branchEffect, condHolds, zf, h, branchTarget]
  obtain ⟨w, runW, readyW, effectW⟩ :=
    (jcc_rel32_effect_step 0x10f16e 4 0x18d).advances readyA
      (programText_slice (programLoaded_codeIn stateA.loaded) 0xf16e
        [0x0f, 0x84, 0x8d, 0x01, 0, 0] (by decide) (by decide +kernel))
      ⟨effectA.rip, by intro h; decide +kernel⟩
      (by rw [next]; split
          · exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf301 (by decide))
          · exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf174 (by decide)))
  have frameW : AgreesExcept [.rip] a w := effectW.agrees
  have frame : AgreesExcept [.flags, .rip] t w := (frameA.trans frameW).mono (by simp)
  exact ⟨w, runA.trans runW, state.after_registers readyW frame (by simp [Component.Covers])
    (by simp), effectW.rip.trans next, frame⟩

end P256.Proofs.Verifying.Combination.Loop.Multi
