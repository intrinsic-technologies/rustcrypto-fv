import P256.Proofs.SecretKeyFromBytes.Scalar.Borrow
import P256.Proofs.Common.Instructions.ByteOps.Effects
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import P256.Proofs.Common.EffectCompose.Memory

set_option autoImplicit false

open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice)

namespace P256.Proofs.SignatureFromDer.Fixed.Scalar

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem length_branch [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (rip : s.RIP = 0x10fa37)
    (status : s.regValue .rdx = 32)
    (outside : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ t.RIP = 0x10fa41 ∧
      AgreesExcept [.flags, .rip] s t := by
  have code := programLoaded_codeIn loaded
  obtain ⟨u, stepU, readyU, effectU⟩ := cmp_r64_imm8_effect_step 0x10fa37 0x48 0xfa 32
    (by simp [RexWPrefix]) rfl rfl s ready
    (programText_slice code 0xfa37 _ (by decide +kernel) (by decide +kernel)) rip
  have zf : (StatusFlags.ofRFLAGS u.RFLAGS).ZF = true := by
    have h := effectU.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
      (cmpSpec (s.regValue .rdx) (32 : BitVec 64)).ZF at h
    rw [status] at h
    exact h
  have memory : u.external = s.external := effectU.agrees.external
    (by simp [cmpR64Imm8Effect, Effect.components, Component.Covers])
  obtain ⟨t, stepT, readyT, rawT⟩ := jcc_rel32_effect_step 0x10fa3b 5 0x14f u readyU
    (programText_slice (code.of_external_eq memory) 0xfa3b _
      (by decide +kernel) (by decide +kernel)) ⟨effectU.rip, fun _ => by decide +kernel⟩
  have effectT := jccEffect_not_taken
    (show condHolds 5 (StatusFlags.ofRFLAGS u.RFLAGS) = false from by
      change (!(StatusFlags.ofRFLAGS u.RFLAGS).ZF) = false
      rw [zf]
      rfl) rawT
  have runU : Advances boundary 1 s u := Advances.of_step stepU (.inl (by
    rw [effectU.rip]
    exact boundary_ne_program outside (inProgram_of_textOffset 0xfa3b (by decide))))
  have runT : Advances boundary 1 u t := Advances.of_step stepT (.inl (by
    rw [effectT.rip]
    exact boundary_ne_program outside (inProgram_of_textOffset 0xfa41 (by decide))))
  refine ⟨t, runU.trans runT, readyT, effectT.rip, ?_⟩
  exact (effectU.agrees.trans effectT.agrees).mono
    (by simp [cmpR64Imm8Effect, nopEffect, Effect.components])

end P256.Proofs.SignatureFromDer.Fixed.Scalar
