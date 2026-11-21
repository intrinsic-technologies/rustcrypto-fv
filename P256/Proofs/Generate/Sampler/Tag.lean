import P256.Proofs.Generate.Sampler.Setup
import P256.Proofs.Generate.Sampler.Memory
import P256.Proofs.Common.Der.Decode.Header.Control
import P256.Proofs.SignatureFromDer.Parser.Assert.Execution
import X86Proofs.Instructions.Cmp.Generated.M8Imm8.Triple

set_option autoImplicit false

namespace P256.Proofs.Generate.Sampler

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SignatureFromDer.Parser.ReadSlice
open P256.Proofs.Common.Der.Decode.Header

theorem tag_branch [Bindings] {s t : RamState} {boundary : ReturnBoundary} {input : ByteArray}
    (pre : Pre s boundary input) (state : State s t) (rip : t.RIP = 0x100cda) :
    ∃ u, (∃ fuel, Advances boundary fuel t u) ∧ State s u ∧
      u.RIP = (if memLoad t.external (stackPtr t+112#64) 8 = 1 then 0x100c00 else 0x100ce5) ∧
      AgreesExcept [.flags,.rip] t u := by
  obtain ⟨a,runA,readyA,_,effectA⟩ := SignatureFromDer.Parser.Assert.advanceText 0xcda
    (cmp_m8_imm8_effect_step 0x100cda (.sib 4 none 0 (.d8 112))
      (by decide) (by decide) (by decide) 1)
    (by decide +kernel) (by decide) (readyToStep state.machine state.bindingsSupported)
    (programLoaded_codeIn state.loaded) ⟨rip,state.stack_readable pre (by decide)⟩
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xcdf (by decide)))
    (Effect.Avoids.of_noMem (by simp [Component.Covers]) _)
  have sa := state.after_registers pre readyA effectA.agrees
    (by simp [cmpM8Imm8Effect,Effect.components,Component.Covers]) (by simp [cmpM8Imm8Effect,Effect.components])
  by_cases eq : memLoad t.external (stackPtr t+112#64) 8 = 1
  · have flag : (StatusFlags.ofRFLAGS a.RFLAGS).ZF = true := by
      have h := effectA.flags.2.2.2.1
      change (StatusFlags.ofRFLAGS a.RFLAGS).ZF =
        (cmpSpec (memLoad t.external (stackPtr t+112#64) 8) 1).ZF at h
      rw [h,cmpSpec_ZF,eq]
      rfl
    obtain ⟨u,runU,readyU,_,effectU⟩ := SignatureFromDer.Parser.Assert.advanceText 0xcdf
      (jcc_rel32_taken_effect_step 0x100cdf 4 0xffffff1b (by decide))
      (by decide +kernel) (by decide) readyA (programLoaded_codeIn sa.loaded)
      ⟨effectA.rip,flag⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xc00 (by decide)))
      (jmpEffect_avoids _ _ _ _)
    refine ⟨u,⟨_,runA.trans runU⟩,sa.after_registers pre readyU effectU.agrees
      (by simp [jmpEffect,Effect.components,Component.Covers]) (by simp [jmpEffect,Effect.components]),?_,?_⟩
    · simp only [ite_eq_left eq]
      exact effectU.rip
    · exact (effectA.agrees.trans effectU.agrees).mono (by simp)
  · have flag : (StatusFlags.ofRFLAGS a.RFLAGS).ZF = false := by
      have h := effectA.flags.2.2.2.1
      change (StatusFlags.ofRFLAGS a.RFLAGS).ZF =
        (cmpSpec (memLoad t.external (stackPtr t+112#64) 8) 1).ZF at h
      rw [h,cmpSpec_ZF]
      exact beq_eq_false_iff_ne.mpr eq
    obtain ⟨u,runU,readyU,_,effectU⟩ := SignatureFromDer.Parser.Assert.advanceText 0xcdf
      (jcc_rel32_not_taken_effect_step 0x100cdf 4 0xffffff1b)
      (by decide +kernel) (by decide) readyA (programLoaded_codeIn sa.loaded)
      ⟨effectA.rip,flag⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xce5 (by decide)))
      (nopEffect_avoids _ _ _)
    refine ⟨u,⟨_,runA.trans runU⟩,sa.after_registers pre readyU effectU.agrees
      (by simp [nopEffect,Effect.components,Component.Covers]) (by simp [nopEffect,Effect.components]),?_,?_⟩
    · simp only [ite_eq_right eq]
      exact effectU.rip
    · exact (effectA.agrees.trans effectU.agrees).mono (by simp)

end P256.Proofs.Generate.Sampler
