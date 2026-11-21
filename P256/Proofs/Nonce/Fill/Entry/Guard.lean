import P256.Proofs.Nonce.Fill.Frame
import X86Proofs.Instructions.Cmp.Generated.Imm32.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Entry

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem guard [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (rip : s.RIP = 0x10734d)
    (count : s.regValue .rdx = 32) (outside : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ t.RIP = 0x10735a ∧
      AgreesExcept [.flags, .rip] s t := by
  have code := programLoaded_codeIn loaded
  obtain ⟨a, stepA, readyA, ea⟩ := cmp_r64_imm32_effect_step 0x10734d 0x48 0xfa 0x1fffffff
    (by simp [RexWPrefix]) rfl rfl s ready
    (programText_slice code 0x734d _ (by decide +kernel) (by decide +kernel)) rip
  have cf : (StatusFlags.ofRFLAGS a.RFLAGS).CF = true := by
    have h := ea.flags.1
    change (StatusFlags.ofRFLAGS a.RFLAGS).CF = (cmpSpec (s.regValue .rdx) 0x1fffffff).CF at h
    rw [count] at h
    exact h
  have am : a.external = s.external := ea.agrees.external (by simp [Component.Covers])
  obtain ⟨t, stepT, readyT, etRaw⟩ := jcc_rel32_effect_step 0x107354 7 0x400 a readyA
    (programText_slice (code.of_external_eq am) 0x7354 _
      (by decide +kernel) (by decide +kernel)) ⟨ea.rip, fun _ => by decide +kernel⟩
  have et := jccEffect_not_taken (show condHolds 7 (StatusFlags.ofRFLAGS a.RFLAGS) = false by
    change (!((StatusFlags.ofRFLAGS a.RFLAGS).CF || (StatusFlags.ofRFLAGS a.RFLAGS).ZF)) = false
    rw [cf]; rfl) etRaw
  have ra : Advances boundary 1 s a := Advances.of_step stepA (.inl (by
    rw [ea.rip]; exact boundary_ne_program outside (inProgram_of_textOffset 0x7354 (by decide))))
  have rt : Advances boundary 1 a t := Advances.of_step stepT (.inl (by
    rw [et.rip]; exact boundary_ne_program outside (inProgram_of_textOffset 0x735a (by decide))))
  refine ⟨t, ra.trans rt, readyT, et.rip, ?_⟩
  exact (ea.agrees.trans et.agrees).mono
    (by simp (config := { decide := true }) [cmpR64Imm32Effect, nopEffect, Effect.components])

end P256.Proofs.Nonce.Fill.Entry
