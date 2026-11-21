import P256.Proofs.Nonce.Initialize.Prepare.Memory
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm32.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Prepare.Length

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem guards [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (rip : s.RIP = 0x107858)
    (r8 : s.regValue .r8 = 32) (outside : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 5 s t ∧ ReadyToStep t ∧ t.RIP = 0x107872 ∧
      AgreesExcept [.reg 7, .flags, .rip] s t := by
  have code := programLoaded_codeIn loaded
  obtain ⟨a, stepA, readyA, ea⟩ := mov_r64_r64_effect_step 0x107858 0x4c 0xc7
    (by simp [RexWPrefix]) rfl s ready
    (programText_slice code 0x7858 _ (by decide +kernel) (by decide +kernel)) rip
  have av : a.regValue .rdi = 32 := ea.writes.trans r8
  have am : a.external = s.external := ea.agrees.external (by simp [Component.Covers])
  obtain ⟨b, stepB, readyB, eb⟩ := shr_r64_imm8_effect_step 0x10785b 0x48 0xef 0x20
    (by simp [RexWPrefix]) rfl rfl a readyA
    (programText_slice (code.of_external_eq am) 0x785b _
      (by decide +kernel) (by decide +kernel)) ea.rip
  have zf : (StatusFlags.ofRFLAGS b.RFLAGS).ZF = true := by
    have h := eb.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS b.RFLAGS).ZF = ((a.regValue .rdi >>> (32 : Nat)) == 0) at h
    rw [av] at h
    exact h
  have bm : b.external = s.external :=
    (eb.agrees.external (by simp [Component.Covers])).trans am
  obtain ⟨c, stepC, readyC, ecRaw⟩ := jcc_rel32_effect_step 0x10785f 5 0x42b b readyB
    (programText_slice (code.of_external_eq bm) 0x785f _
      (by decide +kernel) (by decide +kernel)) ⟨eb.rip, fun _ => by decide +kernel⟩
  have ec := jccEffect_not_taken (show condHolds 5 (StatusFlags.ofRFLAGS b.RFLAGS) = false by
    change (!(StatusFlags.ofRFLAGS b.RFLAGS).ZF) = false
    rw [zf]; rfl) ecRaw
  have cm : c.external = s.external :=
    (ec.agrees.external (by simp [Component.Covers])).trans bm
  have cv : c.regValue .r8 = 32 :=
    ((ea.agrees.trans eb.agrees |>.trans ec.agrees).read (n := 64) (r := 8)
      (by simp (config := { decide := true }) [movR64R64Effect, shrR64Effect, nopEffect, Effect.components])).trans r8
  obtain ⟨d, stepD, readyD, ed⟩ := cmp_r64_imm32_effect_step 0x107865 0x49 0xf8 0x1fffffff
    (by simp [RexWPrefix]) rfl rfl c readyC
    (programText_slice (code.of_external_eq cm) 0x7865 _
      (by decide +kernel) (by decide +kernel)) ec.rip
  have cf : (StatusFlags.ofRFLAGS d.RFLAGS).CF = true := by
    have h := ed.flags.1
    change (StatusFlags.ofRFLAGS d.RFLAGS).CF = (cmpSpec (c.regValue .r8) 0x1fffffff).CF at h
    rw [cv] at h
    exact h
  have dm : d.external = s.external :=
    (ed.agrees.external (by simp [Component.Covers])).trans cm
  obtain ⟨t, stepT, readyT, etRaw⟩ := jcc_rel32_effect_step 0x10786c 7 0x41e d readyD
    (programText_slice (code.of_external_eq dm) 0x786c _
      (by decide +kernel) (by decide +kernel)) ⟨ed.rip, fun _ => by decide +kernel⟩
  have et := jccEffect_not_taken (show condHolds 7 (StatusFlags.ofRFLAGS d.RFLAGS) = false by
    change (!((StatusFlags.ofRFLAGS d.RFLAGS).CF || (StatusFlags.ofRFLAGS d.RFLAGS).ZF)) = false
    rw [cf]; rfl) etRaw
  have ra : Advances boundary 1 s a := Advances.of_step stepA (.inl (by
    rw [ea.rip]; exact boundary_ne_program outside (inProgram_of_textOffset 0x785b (by decide))))
  have rb : Advances boundary 1 a b := Advances.of_step stepB (.inl (by
    rw [eb.rip]; exact boundary_ne_program outside (inProgram_of_textOffset 0x785f (by decide))))
  have rc : Advances boundary 1 b c := Advances.of_step stepC (.inl (by
    rw [ec.rip]; exact boundary_ne_program outside (inProgram_of_textOffset 0x7865 (by decide))))
  have rd : Advances boundary 1 c d := Advances.of_step stepD (.inl (by
    rw [ed.rip]; exact boundary_ne_program outside (inProgram_of_textOffset 0x786c (by decide))))
  have rt : Advances boundary 1 d t := Advances.of_step stepT (.inl (by
    rw [et.rip]; exact boundary_ne_program outside (inProgram_of_textOffset 0x7872 (by decide))))
  refine ⟨t, (((ra.trans rb).trans rc).trans rd).trans rt, readyT, et.rip, ?_⟩
  exact ((((ea.agrees.trans eb.agrees).trans ec.agrees).trans ed.agrees).trans et.agrees).mono
    (by simp (config := { decide := true }) [movR64R64Effect, shrR64Effect, cmpR64Imm32Effect, nopEffect, Effect.components])

end P256.Proofs.Nonce.Initialize.Prepare.Length
