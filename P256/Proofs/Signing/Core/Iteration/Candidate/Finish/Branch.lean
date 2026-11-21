import P256.Proofs.Signing.Core.Iteration.Memory
import P256.Proofs.Common.Instructions.ByteOps.Effects
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

open P256.Proofs.Common.Instructions.ByteOps.ByteOps (cmpAlImm8Effect cmp_al_imm8_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice)

namespace P256.Proofs.Signing.Core.Iteration.Candidate.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem accept [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (rip : s.RIP = 0x10cbe5)
    (status : (Operand.reg 0 : Operand 8).read s = 1)
    (outside : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ t.RIP = 0x10cbed ∧
      AgreesExcept [.flags, .rip] s t := by
  have code := programLoaded_codeIn loaded
  obtain ⟨u, stepU, readyU, effectU⟩ := cmp_al_imm8_effect_step 0x10cbe5 1 s ready
    (programText_slice code 0xcbe5 _ (by decide +kernel) (by decide +kernel)) rip
  have zf : (StatusFlags.ofRFLAGS u.RFLAGS).ZF = true := by
    have h := effectU.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
      (cmpSpec ((Operand.reg 0 : Operand 8).read s) 1).ZF at h
    rw [status] at h
    exact h
  have memory : u.external = s.external := effectU.agrees.external
    (by simp [cmpAlImm8Effect, Effect.components, Component.Covers])
  obtain ⟨t, stepT, readyT, rawT⟩ := jcc_rel32_effect_step 0x10cbe7 5 0xfffffeb8 u readyU
    (programText_slice (code.of_external_eq memory) 0xcbe7 _
      (by decide +kernel) (by decide +kernel)) ⟨effectU.rip, fun _ => by decide +kernel⟩
  have effectT := jccEffect_not_taken
    (show condHolds 5 (StatusFlags.ofRFLAGS u.RFLAGS) = false from by
      change (!(StatusFlags.ofRFLAGS u.RFLAGS).ZF) = false
      rw [zf]
      rfl) rawT
  have runU : Advances boundary 1 s u := Advances.of_step stepU (.inl (by
    rw [effectU.rip]
    exact boundary_ne_program outside (inProgram_of_textOffset 0xcbe7 (by decide))))
  have runT : Advances boundary 1 u t := Advances.of_step stepT (.inl (by
    rw [effectT.rip]
    exact boundary_ne_program outside (inProgram_of_textOffset 0xcbed (by decide))))
  refine ⟨t, runU.trans runT, readyT, effectT.rip, ?_⟩
  exact (effectU.agrees.trans effectT.agrees).mono
    (by simp [cmpAlImm8Effect, nopEffect, Effect.components])

end P256.Proofs.Signing.Core.Iteration.Candidate.Finish
