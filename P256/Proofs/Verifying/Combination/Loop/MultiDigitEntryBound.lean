import P256.Proofs.Verifying.Combination.Loop.MultiNegative.State
import X86Proofs.Instructions.Cmp.Generated.Imm32.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem enter_digits [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64} {p q point : Projective} {u v k : Nat}
    (pre : MultiPre s boundary tables digits)
    (state : DigitState s t tables digits p q u v k point true 0x10f1b2)
    (bound : k ≤ 257) :
    ∃ w, Advances boundary 2 t w ∧ DigitState s w tables digits p q u v k point true := by
  obtain ⟨a, runA, readyA, effectA⟩ :=
    (cmp_r64_imm32_effect_step 0x10f1b2 0x48 0xfb 257 (by simp [RexWPrefix]) rfl rfl).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0xf1b2 _
        (by decide) (by decide +kernel)) state.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf1b9 (by decide)))
  have frameA : AgreesExcept [.flags, .rip] t a := effectA.agrees
  have stateA := state.toDigitData.after_registers readyA frameA (by simp [Component.Covers]) (by simp)
  have cf := effectA.flags.1
  have zf := effectA.flags.2.2.2.1
  change (StatusFlags.ofRFLAGS a.RFLAGS).CF = (cmpSpec (t.regValue .rbx) 257).CF at cf
  change (StatusFlags.ofRFLAGS a.RFLAGS).ZF = (cmpSpec (t.regValue .rbx) 257).ZF at zf
  have condition : condHolds 6 (StatusFlags.ofRFLAGS a.RFLAGS) = true := by
    change ((StatusFlags.ofRFLAGS a.RFLAGS).CF || (StatusFlags.ofRFLAGS a.RFLAGS).ZF) = true
    rw [cf, zf, state.count]
    exact (show ∀ i : Fin 258, ((cmpSpec (BitVec.ofNat 64 i.val) 257).CF ||
      (cmpSpec (BitVec.ofNat 64 i.val) 257).ZF) = true by decide +kernel) ⟨k, by omega⟩
  have target : (jccEffect 0x10f1b9 6 6 ((0x110 : BitVec 32).signExtend 64) a).rip = 0x10f2cf := by
    simp only [jccEffect, branchEffect, condition]
    rfl
  obtain ⟨w, runW, readyW, effectW⟩ :=
    (jcc_rel32_effect_step 0x10f1b9 6 0x110).advances readyA
      (programText_slice (programLoaded_codeIn stateA.loaded) 0xf1b9 _
        (by decide) (by decide +kernel))
      ⟨effectA.rip, by intro h; decide +kernel⟩
      (by
        rw [target]
        exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf2cf (by decide)))
  have frameW : AgreesExcept [.rip] a w := effectW.agrees
  have frame : AgreesExcept [.flags, .rip] t w := (frameA.trans frameW).mono (by simp)
  refine ⟨w, runA.trans runW, ⟨state.toDigitData.after_registers readyW frame
    (by simp [Component.Covers]) (by simp), effectW.rip.trans target, ?_⟩⟩
  intro h
  have eq : w.regValue .r14 = t.regValue .r14 := frame.read (n := 64) (r := 14) (by simp)
  exact state.identity (by rwa [eq] at h)

end P256.Proofs.Verifying.Combination.Loop.Multi
