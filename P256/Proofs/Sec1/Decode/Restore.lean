import P256.Proofs.Program.Code
import P256.Proofs.Program.Pop

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decode

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem restore_registers [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (outside : ¬ InProgram boundary.rip) (rip : s.RIP = 0x10e6a0)
    (readable : ∀ off ∈ ([0, 8, 16, 24] : List Nat),
      MemReadable s (stackPtr s + BitVec.ofNat 64 off) 8) :
    ∃ t, Advances boundary 4 s t ∧ ReadyToStep t ∧ t.RIP = 0x10e6a7 ∧
      stackPtr t = stackPtr s + 32 ∧ t.external = s.external ∧
      AgreesExcept [.reg 3, .reg 12, .reg 14, .reg 15, .reg 4, .rip] s t ∧
      t.regValue .rbx = memLoad s.external (stackPtr s) 64 ∧
      t.regValue .r12 = memLoad s.external (stackPtr s + 8) 64 ∧
      t.regValue .r14 = memLoad s.external (stackPtr s + 16) 64 ∧
      t.regValue .r15 = memLoad s.external (stackPtr s + 24) 64 := by
  obtain ⟨s1, a1, r1, e1⟩ :=
    (pop_register_effect_step 0x10e6a0 3 (by decide)).advances ready
      (programText_slice (programLoaded_codeIn loaded) 0xe6a0 (encodePopR64 3)
        (by decide) (by decide +kernel))
      ⟨rip, by simpa only [BitVec.add_zero] using readable 0 (by simp)⟩
      (boundary_ne_program outside (inProgram_of_textOffset 0xe6a1 (by decide)))
  have g1 : AgreesExcept [.reg 3, .reg 4, .rip] s s1 := e1.agrees
  have m1 : s1.external = s.external :=
    g1.external (by simp [Component.Covers])
  have sp1 : stackPtr s1 = stackPtr s + 8 := by
    have hw : stackPtr s1 = stackPtr s + 8 := e1.writes.2
    exact hw
  have v1 : s1.regValue .rbx = memLoad s.external (stackPtr s) 64 := by
    have hw : s1.regValue .rbx = memLoad s.external (stackPtr s) 64 := e1.writes.1
    exact hw
  obtain ⟨s2, a2, r2, e2⟩ :=
    (pop_register_effect_step 0x10e6a1 12 (by decide)).advances r1
      (programText_slice ((programLoaded_codeIn loaded).of_external_eq m1) 0xe6a1 (encodePopR64 12)
        (by decide) (by decide +kernel))
      ⟨e1.rip, by rw [sp1]; exact (readable 8 (by simp)).of_external_eq m1⟩
      (boundary_ne_program outside (inProgram_of_textOffset 0xe6a3 (by decide)))
  have g2 : AgreesExcept [.reg 12, .reg 4, .rip] s1 s2 := e2.agrees
  have m2 : s2.external = s.external :=
    (g2.external (by simp [Component.Covers])).trans m1
  have sp2 : stackPtr s2 = stackPtr s + 16 := by
    have hw : stackPtr s2 = stackPtr s1 + 8 := e2.writes.2
    rw [hw, sp1, BitVec.add_assoc]
    rfl
  have v2 : s2.regValue .r12 = memLoad s.external (stackPtr s + 8) 64 := by
    have hw : s2.regValue .r12 = memLoad s1.external (stackPtr s1) 64 := e2.writes.1
    rwa [m1, sp1] at hw
  obtain ⟨s3, a3, r3, e3⟩ :=
    (pop_register_effect_step 0x10e6a3 14 (by decide)).advances r2
      (programText_slice ((programLoaded_codeIn loaded).of_external_eq m2) 0xe6a3 (encodePopR64 14)
        (by decide) (by decide +kernel))
      ⟨e2.rip, by rw [sp2]; exact (readable 16 (by simp)).of_external_eq m2⟩
      (boundary_ne_program outside (inProgram_of_textOffset 0xe6a5 (by decide)))
  have g3 : AgreesExcept [.reg 14, .reg 4, .rip] s2 s3 := e3.agrees
  have m3 : s3.external = s.external :=
    (g3.external (by simp [Component.Covers])).trans m2
  have sp3 : stackPtr s3 = stackPtr s + 24 := by
    have hw : stackPtr s3 = stackPtr s2 + 8 := e3.writes.2
    rw [hw, sp2, BitVec.add_assoc]
    rfl
  have v3 : s3.regValue .r14 = memLoad s.external (stackPtr s + 16) 64 := by
    have hw : s3.regValue .r14 = memLoad s2.external (stackPtr s2) 64 := e3.writes.1
    rwa [m2, sp2] at hw
  obtain ⟨s4, a4, r4, e4⟩ :=
    (pop_register_effect_step 0x10e6a5 15 (by decide)).advances r3
      (programText_slice ((programLoaded_codeIn loaded).of_external_eq m3) 0xe6a5 (encodePopR64 15)
        (by decide) (by decide +kernel))
      ⟨e3.rip, by rw [sp3]; exact (readable 24 (by simp)).of_external_eq m3⟩
      (boundary_ne_program outside (inProgram_of_textOffset 0xe6a7 (by decide)))
  have g4 : AgreesExcept [.reg 15, .reg 4, .rip] s3 s4 := e4.agrees
  have m4 : s4.external = s.external :=
    (g4.external (by simp [Component.Covers])).trans m3
  have sp4 : stackPtr s4 = stackPtr s + 32 := by
    have hw : stackPtr s4 = stackPtr s3 + 8 := e4.writes.2
    rw [hw, sp3, BitVec.add_assoc]
    rfl
  have v4 : s4.regValue .r15 = memLoad s.external (stackPtr s + 24) 64 := by
    have hw : s4.regValue .r15 = memLoad s3.external (stackPtr s3) 64 := e4.writes.1
    rwa [m3, sp3] at hw
  refine ⟨s4, ((a1.trans a2).trans a3).trans a4, r4, e4.rip, sp4, m4,
    (((g1.trans g2).trans g3).trans g4).mono (by simp), ?_, ?_, ?_, v4⟩
  · exact (((g2.trans g3).trans g4).read (n := 64) (r := 3) (by simp)).trans v1
  · exact ((g3.trans g4).read (n := 64) (r := 12) (by simp)).trans v2
  · exact (g4.read (n := 64) (r := 14) (by simp)).trans v3

end P256.Proofs.Sec1.Decode
