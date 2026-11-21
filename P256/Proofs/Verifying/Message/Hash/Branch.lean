import P256.Proofs.Program.Code
import X86Proofs.Instructions.Test.Generated.RR.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem entry_branch [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (rip : s.RIP = 0x10d5f5)
    (count : s.regValue .rcx = 1) (outside : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ t.RIP = 0x10d5fe ∧
      AgreesExcept [.flags, .rip] s t := by
  obtain ⟨u, hu, hru, heu⟩ :=
    (test_r64_r64_effect_step 0x10d5f5 0x48 0xc9 (by constructor <;> rfl) rfl).advances
      ready
      (programText_slice (programLoaded_codeIn loaded) 0xd5f5
        [0x48,0x85,0xc9] (by decide +kernel) (by decide +kernel)) rip
      (boundary_ne_program outside (inProgram_of_textOffset 0xd5f8 (by decide +kernel)))
  have hfu : AgreesExcept [.flags,.rip] s u := heu.agrees
  have zf : (StatusFlags.ofRFLAGS u.RFLAGS).ZF = (s.regValue .rcx == 0) := by
    have h := heu.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS u.RFLAGS).ZF = ((s.regValue .rcx &&& s.regValue .rcx) == 0) at h
    simpa only [BitVec.and_self] using h
  obtain ⟨t, step, hrt, het⟩ := jcc_rel32_effect_step 0x10d5f8 4 0x11f u hru
    (programText_slice (hfu.codeIn (by simp [Component.Covers]) (programLoaded_codeIn loaded))
      0xd5f8 [0x0f,0x84,0x1f,0x01,0,0] (by decide +kernel) (by decide +kernel))
    ⟨heu.rip, fun _ => by decide +kernel⟩
  have ht : t.RIP = 0x10d5fe := by
    rw [het.rip]
    change (if (StatusFlags.ofRFLAGS u.RFLAGS).ZF then (0x10d71d : BitVec 64) else 0x10d5fe) = _
    rw [zf, count]
    rfl
  have ha : Advances boundary 1 u t := Advances.of_step step (.inl (by
    rw [ht]
    exact boundary_ne_program outside (inProgram_of_textOffset 0xd5fe (by decide))))
  have hft : AgreesExcept [.rip] u t := het.agrees
  exact ⟨t, hu.trans ha, hrt, ht, (hfu.trans hft).mono (by simp)⟩

end P256.Proofs.Verifying.Message.Hash
