import P256.Proofs.Nonce.Fill.Tail.Decode.State
import P256.Proofs.Common.Instructions.ByteOps.Effects
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Tail.Decode

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Instructions.ByteOps.ByteOps

theorem guard [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (rip : s.RIP = 0x107528)
    (status : (Operand.reg 0 : Operand 8).read s = 255) (outside : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ t.RIP = 0x107530 ∧
      AgreesExcept [.flags, .rip] s t := by
  obtain ⟨a, aa, ar, ae⟩ := (cmp_al_imm8_effect_step 0x107528 255).advances ready
    (programText_slice (programLoaded_codeIn loaded) 0x7528 _
      (by decide +kernel) (by decide +kernel)) rip
    (boundary_ne_program outside (inProgram_of_textOffset 0x752a (by decide)))
  have ag : AgreesExcept [.flags, .rip] s a := ae.agrees
  have zf : (StatusFlags.ofRFLAGS a.RFLAGS).ZF = true := by
    have h := ae.flag .ZF
    change (StatusFlags.ofRFLAGS a.RFLAGS).ZF = (cmpSpec ((Operand.reg 0 : Operand 8).read s) 255).ZF at h
    rw [status] at h
    exact h
  have am := ag.external (by simp [Component.Covers])
  obtain ⟨t, step, tr, raw⟩ := jcc_rel32_effect_step 0x10752a 5 0x1ed a ar
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq am) 0x752a _
      (by decide +kernel) (by decide +kernel)) ⟨ae.rip, fun _ => by decide +kernel⟩
  have te := jccEffect_not_taken (show condHolds 5 (StatusFlags.ofRFLAGS a.RFLAGS) = false by
    change (!(StatusFlags.ofRFLAGS a.RFLAGS).ZF) = false
    rw [zf]; rfl) raw
  have ta : Advances boundary 1 a t := Advances.of_step step (.inl (by
    rw [te.rip]
    exact boundary_ne_program outside (inProgram_of_textOffset 0x7530 (by decide))))
  exact ⟨t, aa.trans ta, tr, te.rip, (ag.trans te.agrees).mono (by simp)⟩

end P256.Proofs.Nonce.Fill.Tail.Decode
