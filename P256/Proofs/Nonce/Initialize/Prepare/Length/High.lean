import P256.Proofs.Nonce.Initialize.Prepare.Length.Guards
import P256.Proofs.Nonce.Initialize.Conversions.Bsr.Effect
import P256.Proofs.Nonce.Initialize.Conversions.XorImmediate
import P256.Proofs.Nonce.Initialize.Conversions.Neg32
import X86Proofs.Instructions.And.Generated.RR.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Prepare.Length

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Nonce.Initialize.Conversions.Neg32 P256.Proofs.Nonce.Initialize.Conversions.Bsr
open P256.Proofs.Nonce.Initialize.Conversions.XorImmediate

theorem high_limb [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (rip : s.RIP = 0x10787f)
    (rbx : s.regValue .rbx = 0xffffffff00000000)
    (outside : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 5 s t ∧ ReadyToStep t ∧ t.RIP = 0x107892 ∧
      t.regValue .rsi = 0 ∧ AgreesExcept [.reg 9, .reg 6, .flags, .rip] s t := by
  have code := programLoaded_codeIn loaded
  obtain ⟨s1, a1, r1, e1⟩ :=
    (mov_r32_imm32_rex_effect_step 0x10787f 0x41 0xb9 (by simp [RexNoWPrefix]) (by decide) 127).advances ready
      (programText_slice code 0x787f _ (by decide +kernel) (by decide +kernel)) rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x7885 (by decide)))
  have g1 : AgreesExcept [.reg 9, .rip] s s1 := e1.agrees
  have m1 : s1.external = s.external := g1.external (by simp [Component.Covers])
  have nine1 : s1.regValue .r9 = 127 := e1.writes
  have high1 : s1.regValue .rbx = 0xffffffff00000000 :=
    (g1.read (n := 64) (r := 3) (by simp)).trans rbx
  obtain ⟨s2, a2, r2, e2⟩ :=
    (bsr_r64_r64_effect_step 0x107885 0x4c 0xcb (by simp [RexWPrefix]) rfl).advances r1
      (programText_slice (code.of_external_eq m1) 0x7885 _ (by decide +kernel) (by decide +kernel)) e1.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x7889 (by decide)))
  have g2 : AgreesExcept [.reg 9, .flags, .rip] s1 s2 := e2.agrees
  have m2 : s2.external = s.external := (g2.external (by simp [Component.Covers])).trans m1
  have nine2 : s2.regValue .r9 = 63 := by
    have h : s2.regValue .r9 = (bsrSpec64 (s1.regValue .r9) (s1.regValue .rbx)).1 := e2.writes
    rw [nine1, high1] at h
    exact h.trans (by decide +kernel)
  obtain ⟨s3, a3, r3, e3⟩ :=
    (xor_r32_imm8_rex_effect_step 0x107889 0x41 0xf1 63 (by simp [RexNoWPrefix]) rfl rfl).advances r2
      (programText_slice (code.of_external_eq m2) 0x7889 _ (by decide +kernel) (by decide +kernel)) e2.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x788d (by decide)))
  have g3 : AgreesExcept [.reg 9, .flags, .rip] s2 s3 := e3.agrees
  have m3 : s3.external = s.external := (g3.external (by simp [Component.Covers])).trans m2
  have nine3 : s3.regValue .r9 = 0 := by
    have h : s3.regValue .r9 = (((s2.regValue .r9).setWidth 32) ^^^ 63).setWidth 64 := e3.writes
    rwa [nine2] at h
  obtain ⟨s4, a4, r4, e4⟩ :=
    (neg_r32_effect_step 0x10788d 0xde rfl rfl).advances r3
      (programText_slice (code.of_external_eq m3) 0x788d _ (by decide +kernel) (by decide +kernel)) e3.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x788f (by decide)))
  have g4 : AgreesExcept [.reg 6, .flags, .rip] s3 s4 := e4.agrees
  have m4 : s4.external = s.external := (g4.external (by simp [Component.Covers])).trans m3
  have nine4 : s4.regValue .r9 = 0 := (g4.read (n := 64) (r := 9) (by simp)).trans nine3
  obtain ⟨s5, a5, r5, e5⟩ :=
    (and_r32_r32_rex_effect_step 0x10788f 0x44 0xce (by simp [RexNoWPrefix]) rfl).advances r4
      (programText_slice (code.of_external_eq m4) 0x788f _ (by decide +kernel) (by decide +kernel)) e4.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x7892 (by decide)))
  have g5 : AgreesExcept [.reg 6, .flags, .rip] s4 s5 := e5.agrees
  refine ⟨s5, (((a1.trans a2).trans a3).trans a4).trans a5, r5, e5.rip, ?_, ?_⟩
  · have h : s5.regValue .rsi = ((s4.regValue .rsi).setWidth 32 &&&
        (s4.regValue .r9).setWidth 32).setWidth 64 := e5.writes
    simpa [nine4] using h
  · exact ((((g1.trans g2).trans g3).trans g4).trans g5).mono (by simp)

end P256.Proofs.Nonce.Initialize.Prepare.Length
