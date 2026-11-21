import P256.Proofs.Generate.Sampler.Setup
import P256.Proofs.Generate.Sampler.Memory
import P256.Proofs.Common.Der.Decode.Header.Control
import P256.Proofs.SignatureFromDer.Parser.Assert.Execution
import P256.Proofs.Common.Instructions.ByteOps.Effects
import X86Proofs.Instructions.Add.Generated.Imm8.Triple

set_option autoImplicit false

namespace P256.Proofs.Generate.Sampler.Nonzero

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SignatureFromDer.Parser.ReadSlice
open P256.Proofs.Common.Der.Decode.Header

theorem branch [Bindings] {s t : RamState} {boundary : ReturnBoundary} {input : ByteArray}
    (pre : Pre s boundary input) (state : State s t) (rip : t.RIP = 0x100c8c) :
    ∃ u, (∃ fuel, Advances boundary fuel t u) ∧ State s u ∧
      u.RIP = (if (t.regValue .rax).setWidth 8 = 1 then 0x100d1d else 0x100c94) ∧
      AgreesExcept [.flags,.rip] t u := by
  obtain ⟨a,runA,readyA,_,effectA⟩ := SignatureFromDer.Parser.Assert.advanceText 0xc8c
    (P256.Proofs.Common.Instructions.ByteOps.ByteOps.cmp_al_imm8_effect_step 0x100c8c 1)
    (by decide +kernel) (by decide) (readyToStep state.machine state.bindingsSupported)
    (programLoaded_codeIn state.loaded) rip
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xc8e (by decide)))
    (Effect.Avoids.of_noMem (by simp [P256.Proofs.Common.Instructions.ByteOps.ByteOps.cmpAlImm8Effect,Effect.components,Component.Covers]) _)
  have sa := state.after_registers pre readyA effectA.agrees
    (by simp [P256.Proofs.Common.Instructions.ByteOps.ByteOps.cmpAlImm8Effect,Effect.components,Component.Covers]) (by simp [P256.Proofs.Common.Instructions.ByteOps.ByteOps.cmpAlImm8Effect,Effect.components])
  by_cases eq : (t.regValue .rax).setWidth 8 = 1
  · have flag : (StatusFlags.ofRFLAGS a.RFLAGS).ZF = true := by
      have h := effectA.flags.2.2.2.1
      change (StatusFlags.ofRFLAGS a.RFLAGS).ZF =
        (cmpSpec ((t.regValue .rax).setWidth 8) 1).ZF at h
      rw [h,cmpSpec_ZF,eq]
      rfl
    obtain ⟨u,runU,readyU,_,effectU⟩ := SignatureFromDer.Parser.Assert.advanceText 0xc8e
      (jcc_rel32_taken_effect_step 0x100c8e 4 0x89 (by decide))
      (by decide +kernel) (by decide) readyA (programLoaded_codeIn sa.loaded)
      ⟨effectA.rip,flag⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xd1d (by decide)))
      (jmpEffect_avoids _ _ _ _)
    refine ⟨u,⟨_,runA.trans runU⟩,sa.after_registers pre readyU effectU.agrees
      (by simp [jmpEffect,Effect.components,Component.Covers]) (by simp [jmpEffect,Effect.components]),?_,?_⟩
    · simp only [ite_eq_left eq]
      exact effectU.rip
    · exact (effectA.agrees.trans effectU.agrees).mono (by simp [P256.Proofs.Common.Instructions.ByteOps.ByteOps.cmpAlImm8Effect,jmpEffect,Effect.components])
  · have flag : (StatusFlags.ofRFLAGS a.RFLAGS).ZF = false := by
      have h := effectA.flags.2.2.2.1
      change (StatusFlags.ofRFLAGS a.RFLAGS).ZF =
        (cmpSpec ((t.regValue .rax).setWidth 8) 1).ZF at h
      rw [h,cmpSpec_ZF]
      exact beq_eq_false_iff_ne.mpr eq
    obtain ⟨u,runU,readyU,_,effectU⟩ := SignatureFromDer.Parser.Assert.advanceText 0xc8e
      (jcc_rel32_not_taken_effect_step 0x100c8e 4 0x89)
      (by decide +kernel) (by decide) readyA (programLoaded_codeIn sa.loaded)
      ⟨effectA.rip,flag⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xc94 (by decide)))
      (nopEffect_avoids _ _ _)
    refine ⟨u,⟨_,runA.trans runU⟩,sa.after_registers pre readyU effectU.agrees
      (by simp [nopEffect,Effect.components,Component.Covers]) (by simp [nopEffect,Effect.components]),?_,?_⟩
    · simp only [ite_eq_right eq]
      exact effectU.rip
    · exact (effectA.agrees.trans effectU.agrees).mono (by simp [P256.Proofs.Common.Instructions.ByteOps.ByteOps.cmpAlImm8Effect,nopEffect,Effect.components])

theorem decrement [Bindings] {s t : RamState} {boundary : ReturnBoundary} {input : ByteArray}
    (pre : Pre s boundary input) (state : State s t) (rip : t.RIP = 0x100c88) :
    ∃ u, Advances boundary 1 t u ∧ State s u ∧ u.RIP = 0x100c8c ∧
      u.regValue .r13 = t.regValue .r13 - 32 ∧ AgreesExcept [.reg 13,.flags,.rip] t u := by
  obtain ⟨u,h,r,e⟩ := (add_r64_imm8_effect_step 0x100c88 0x49 0xc5 0xe0
    (by simp [RexWPrefix]) rfl rfl).advances
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xc88 _ (by decide) (by decide +kernel)) rip
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xc8c (by decide)))
  have g : AgreesExcept [.reg 13,.flags,.rip] t u := e.agrees
  refine ⟨u,h,state.after_registers pre r g (by simp [Component.Covers]) (by simp),e.rip,?_,g⟩
  have hval := e.writes
  change u.regValue .r13 = t.regValue .r13 + 18446744073709551584#64 at hval
  simpa only [BitVec.sub_eq_add_neg,BitVec.reduceNeg] using hval

end P256.Proofs.Generate.Sampler.Nonzero
