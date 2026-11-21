import P256.Proofs.Nonce.Fill.Frame
import X86Proofs.Instructions.Test.Generated.RR.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.NopMem.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Entry

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem branch [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (rip : s.RIP = 0x107387)
    (count : s.regValue .r13 = 32) (outside : ¬ InProgram boundary.rip)
    (readable : MemReadable s (stackPtr s + 136) 8) :
    ∃ t, Advances boundary 5 s t ∧ ReadyToStep t ∧ t.RIP = 0x1073a0 ∧
      t.regValue .r12 = memLoad s.external (stackPtr s + 136) 64 ∧
      t.regValue .rbx = 0x11c930 ∧ AgreesExcept [.reg 12, .reg 3, .flags, .rip] s t := by
  have code := programLoaded_codeIn loaded
  obtain ⟨a, stepA, readyA, ea⟩ := test_r64_r64_effect_step 0x107387 0x4d 0xed
    (by simp [RexWPrefix]) rfl s ready
    (programText_slice code 0x7387 _ (by decide) (by decide +kernel)) rip
  have zf : (StatusFlags.ofRFLAGS a.RFLAGS).ZF = false := by
    have h := ea.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS a.RFLAGS).ZF = ((s.regValue .r13 &&& s.regValue .r13) == 0) at h
    rw [count] at h
    exact h
  have am : a.external = s.external := ea.agrees.external (by simp [Component.Covers])
  have asp : stackPtr a = stackPtr s := ea.agrees.read (n := 64) (r := 4) (by component_not_mem)
  obtain ⟨b, stepB, readyB, eb⟩ := mov_r64_m64_effect_step 0x10738a 0x4c
    (by simp [RexWPrefix]) 4 (.sib 4 none 0 (.d32 136)) (by decide) rfl rfl a readyA
    (programText_slice (code.of_external_eq am) 0x738a _ (by decide) (by decide +kernel))
    ⟨ea.rip, by
      change MemReadable a (stackPtr a + 136) 8
      rw [asp]
      exact readable.of_external_eq am⟩
  have bm : b.external = s.external := (eb.agrees.external (by simp [Component.Covers])).trans am
  obtain ⟨c, stepC, readyC, ec⟩ := lea_r64_effect_step 0x107392 0x48
    (by simp [RexWPrefix]) 3 (.rip 0x15597) (by decide) rfl rfl b readyB
    (programText_slice (code.of_external_eq bm) 0x7392 _ (by decide) (by decide +kernel)) eb.rip
  have cm : c.external = s.external := (ec.agrees.external (by simp [Component.Covers])).trans bm
  have cz : (StatusFlags.ofRFLAGS c.RFLAGS).ZF = false := by
    rw [← eb.agrees.rflags (by component_not_mem) (by component_not_mem), ← ec.agrees.rflags (by component_not_mem) (by component_not_mem)] at zf
    exact zf
  obtain ⟨d, stepD, readyD, edRaw⟩ := jcc_rel8_effect_step 0x107399 4 0x44 c readyC
    (programText_slice (code.of_external_eq cm) 0x7399 _ (by decide) (by decide +kernel))
    ⟨ec.rip, fun _ => by decide +kernel⟩
  have ed := jccEffect_not_taken (show condHolds 4 (StatusFlags.ofRFLAGS c.RFLAGS) = false from cz) edRaw
  have dm : d.external = s.external := (ed.agrees.external (by simp [Component.Covers])).trans cm
  obtain ⟨t, stepT, readyT, et⟩ := nop_m_effect_step 0x10739b [] (by simp) (by decide)
    (.sib 0 (some 0) 0 (.d8 0)) (by decide) rfl rfl d readyD
    (programText_slice (code.of_external_eq dm) 0x739b _ (by decide) (by decide +kernel)) ed.rip
  have ra : Advances boundary 1 s a := Advances.of_step stepA (.inl (by
    rw [ea.rip]; exact boundary_ne_program outside (inProgram_of_textOffset 0x738a (by decide))))
  have rb : Advances boundary 1 a b := Advances.of_step stepB (.inl (by
    rw [eb.rip]; exact boundary_ne_program outside (inProgram_of_textOffset 0x7392 (by decide))))
  have rc : Advances boundary 1 b c := Advances.of_step stepC (.inl (by
    rw [ec.rip]; exact boundary_ne_program outside (inProgram_of_textOffset 0x7399 (by decide))))
  have rd : Advances boundary 1 c d := Advances.of_step stepD (.inl (by
    rw [ed.rip]; exact boundary_ne_program outside (inProgram_of_textOffset 0x739b (by decide))))
  have rt : Advances boundary 1 d t := Advances.of_step stepT (.inl (by
    rw [et.rip]; exact boundary_ne_program outside (inProgram_of_textOffset 0x73a0 (by decide))))
  refine ⟨t, (((ra.trans rb).trans rc).trans rd).trans rt, readyT, et.rip, ?_, ?_, ?_⟩
  · have keep := ((ec.agrees.trans ed.agrees).trans et.agrees).read (n := 64) (r := 12)
      (by component_not_mem)
    change t.regValue .r12 = b.regValue .r12 at keep
    rw [keep]
    have h : b.regValue .r12 = memLoad a.external (stackPtr a + 136) 64 := eb.writes
    simpa only [am, asp] using h
  · exact ((ed.agrees.trans et.agrees).read (n := 64) (r := 3) (by component_not_mem)).trans ec.writes
  · exact ((((ea.agrees.trans eb.agrees).trans ec.agrees).trans ed.agrees).trans et.agrees).mono
      (by simp (config := { decide := true }) [testR64R64Effect, movR64M64Effect,
        leaR64Effect, nopEffect, Effect.components])

end P256.Proofs.Nonce.Fill.Entry
