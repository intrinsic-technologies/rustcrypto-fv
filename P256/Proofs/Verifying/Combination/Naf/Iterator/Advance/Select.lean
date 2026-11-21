import P256.Proofs.Verifying.Combination.Naf.Iterator.Advance.Branch

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Iterator.Advance

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar

theorem select [Bindings] {s : RamState} {boundary : ReturnBoundary} {r : Nat}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (rip : s.RIP = 0x1181df)
    (remaining : s.regValue .rcx = BitVec.ofNat 64 r) (choices : r = 0 ∨ r = 8 ∨ r = 16)
    (outer : ¬ InProgram boundary.rip) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = (if r = 0 then 0x11823c else 0x11824e) ∧ AgreesExcept [.flags, .rip] s t := by
  obtain ⟨a, runA, readyA, loadedA, effectA⟩ := step_nomem (offset := 0x181df)
    (test_r64_r64_effect_step 0x1181df 0x48 0xc9 (by simp [RexWPrefix]) rfl)
    ready loaded rip (by decide) (by decide +kernel)
    (boundary_ne_program outer (inProgram_of_textOffset 0x181e2 (by decide)))
    (by simp [Component.Covers])
  have zf : (StatusFlags.ofRFLAGS a.RFLAGS).ZF = decide (r=0) := by
    have h := effectA.flags.2.2.2.1
    change _ = ((s.regValue .rcx &&& s.regValue .rcx) == 0) at h
    rw [remaining] at h
    rcases choices with rfl | rfl | rfl <;> simpa using h
  obtain ⟨b, runB, readyB, loadedB, ripB, agB⟩ := branch8 (offset := 0x181e2) 4 0x58 (decide (r=0))
    readyA loadedA effectA.rip zf (by decide) (by decide +kernel) (by decide +kernel) (by
      by_cases he : r=0
      · simpa [he, branchTarget, Extracted.textAddress] using
          boundary_ne_program outer (inProgram_of_textOffset 0x1823c (by decide))
      · simpa [he, branchTarget, Extracted.textAddress] using
          boundary_ne_program outer (inProgram_of_textOffset 0x181e4 (by decide)))
  have frameB : AgreesExcept [.flags, .rip] s b := (effectA.agrees.trans agB).mono (by simp)
  by_cases he : r=0
  · exact ⟨2, b, runA.trans runB, readyB, loadedB,
      by simpa [he, branchTarget, Extracted.textAddress] using ripB, frameB⟩
  · have brip : b.RIP = 0x1181e4 := by simpa [he, branchTarget, Extracted.textAddress] using ripB
    have bc : b.regValue .rcx = BitVec.ofNat 64 r :=
      (frameB.read (n := 64) (r := 1) (by simp)).trans remaining
    obtain ⟨c, runC, readyC, loadedC, effectC⟩ := step_nomem (offset := 0x181e4)
      (cmp_r64_imm8_effect_step 0x1181e4 0x48 0xf9 7 (by simp [RexWPrefix]) rfl rfl)
      readyB loadedB brip (by decide) (by decide +kernel)
      (boundary_ne_program outer (inProgram_of_textOffset 0x181e8 (by decide)))
      (by simp [Component.Covers])
    have condition : condHolds 7 (StatusFlags.ofRFLAGS c.RFLAGS) = true := by
      have cf := effectC.flags.1
      have zf := effectC.flags.2.2.2.1
      change (StatusFlags.ofRFLAGS c.RFLAGS).CF = (b.regValue .rcx).ult 7 at cf
      change (StatusFlags.ofRFLAGS c.RFLAGS).ZF = ((b.regValue .rcx - 7) == 0) at zf
      rw [bc] at cf zf
      rcases choices with hz | rfl | rfl
      · exact (he hz).elim
      all_goals simp [condHolds, cf, zf]
    obtain ⟨t, runT, readyT, loadedT, ripT, agT⟩ := branch8 (offset := 0x181e8) 7 0x64 true
      readyC loadedC effectC.rip condition (by decide) (by decide +kernel) (by decide +kernel)
      (boundary_ne_program outer (inProgram_of_textOffset 0x1824e (by decide)))
    refine ⟨4, t, ((runA.trans runB).trans runC).trans runT, readyT, loadedT, ?_, ?_⟩
    · simpa [he, branchTarget, Extracted.textAddress] using ripT
    · exact ((frameB.trans effectC.agrees).trans agT).mono (by simp)

end P256.Proofs.Verifying.Combination.Naf.Iterator.Advance
