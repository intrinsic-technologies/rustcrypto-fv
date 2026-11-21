import Md5.Proofs.Block.Entry
import Md5.Proofs.Block.Execution

namespace Md5.Proofs.NewEntries.Reset

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Md5.Proofs.Block

structure AfterResetPost (nonempty : Bool) (s t : RamState) : Prop where
  rip : t.RIP = if nonempty then 0x101537 else 0x1015fd
  memcpy : nonempty = true → (.reg 15 : Operand 64).read t = 0x1024b0
  agrees : AgreesExcept [.reg 15, .flags, .rip] s t

def secondLoopSetupEffect (_ : RamState) : Effect where
  rip := 0x101537
  writes := [⟨(.reg 15 : Operand 64), 0x1024b0⟩]

theorem second_loop_setup [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x101503) Extracted.programImage
      secondLoopSetupEffect := by
  intro s hReady hCode hRip
  have hLea := lea_r64_effect_step 0x101503 0x4c (by unfold RexWPrefix; decide)
    7 (.rip 0xfa6) (by decide) (by decide) (by decide)
  obtain ⟨u, hRun₁, hReady₁, hEffect₁⟩ := hLea.advances hReady
    (program_text_slice hCode 0x1503 7 (by decide +kernel)) hRip
    (text_address_ne_return hOutside 0x150a (by decide +kernel))
  have hCode₁ := hEffect₁.agrees.codeIn (by simp [Component.Covers]) hCode
  obtain ⟨t, hRun₂, hReady₂, hEffect₂⟩ :=
    (jmp_rel8_effect_step 0x10150a 0x2b (by decide +kernel)).advances hReady₁
      (program_text_slice hCode₁ 0x150a 2 (by decide +kernel)) hEffect₁.rip
      (text_address_ne_return hOutside 0x1537 (by decide +kernel))
  have hAgrees : AgreesExcept [.reg 15, .rip] s t :=
    (hEffect₁.agrees.trans hEffect₂.agrees).mono (by simp [gprNumber, rexR])
  refine ⟨2, t, hRun₁.trans hRun₂, hReady₂,
    hAgrees.codeIn (by simp [Component.Covers]) hCode, ⟨hEffect₂.rip, ?_, trivial, hAgrees⟩⟩
  have hp : (.reg 15 : Operand 64).read u = 0x1024b0 := hEffect₁.writes
  exact (hEffect₂.agrees.read (r := 15) (n := 64) (by simp)).trans hp

theorem after_reset [Bindings] {boundary : ReturnBoundary}
    (hOutside : ¬ InProgram boundary.rip) {s : RamState} (hReady : ReadyToStep s)
    (hCode : CodeIn Extracted.programImage s) (hRip : s.RIP = 0x1014fa) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧
      AfterResetPost (decide (((Operand.reg 12 : Operand 64).read s).toNat <
        ((Operand.reg 6 : Operand 64).read s).toNat)) s t := by
  have hCmp : StepEffect (fun s ↦ s.RIP = 0x1014fa)
      (codeRange 0x1014fa [0x49, 0x39, 0xf4]) (cmpR64R64Effect 0x1014fa 12 6) :=
    cmp_r64_r64_effect_step 0x1014fa 0x49 0xf4
      (by unfold RexWPrefix; decide) (by decide)
  obtain ⟨u, hCmpRun, hCmpReady, hCmpEffect⟩ := hCmp.advances hReady
    (program_text_slice hCode 0x14fa 3 (by decide +kernel)) hRip
    (text_address_ne_return hOutside 0x14fd (by decide +kernel))
  have hCode₁ := hCmpEffect.codeIn (cmpR64R64Effect_avoids _ _ _ _ _) hCode
  have hCarry : (StatusFlags.ofRFLAGS u.RFLAGS).CF =
      decide (((Operand.reg 12 : Operand 64).read s).toNat <
        ((Operand.reg 6 : Operand 64).read s).toNat) := hCmpEffect.flags.1
  have hNext : (jccEffect 0x1014fd 6 3 ((0xfa#32).signExtend 64) u).rip =
      if ((Operand.reg 12 : Operand 64).read s).toNat <
          ((Operand.reg 6 : Operand 64).read s).toNat then 0x101503 else 0x1015fd := by
    simp [jccEffect, branchEffect, condHolds, hCarry, branchTarget, -Nat.not_lt]
  have hNe : (jccEffect 0x1014fd 6 3 ((0xfa#32).signExtend 64) u).rip ≠ boundary.rip := by
    rw [hNext]
    split
    · exact text_address_ne_return hOutside 0x1503 (by decide +kernel)
    · exact text_address_ne_return hOutside 0x15fd (by decide +kernel)
  obtain ⟨v, hBranchRun, hBranchReady, hBranchEffect⟩ :=
    (jcc_rel32_effect_step 0x1014fd 3 0xfa).advances hCmpReady
      (program_text_slice hCode₁ 0x14fd 6 (by decide +kernel))
      ⟨hCmpEffect.rip, fun _ ↦ by decide +kernel⟩ hNe
  have hBefore : AgreesExcept [.flags, .rip] s v :=
    (hCmpEffect.agrees.trans hBranchEffect.agrees).mono (by simp [jccEffect])
  have hCode₂ := hBefore.codeIn (by simp [Component.Covers]) hCode
  have hPc := hBranchEffect.rip.trans hNext
  by_cases hlt : ((Operand.reg 12 : Operand 64).read s).toNat <
      ((Operand.reg 6 : Operand 64).read s).toNat
  · have hEntry : v.RIP = 0x101503 := by simpa only [ite_eq_left hlt] using hPc
    obtain ⟨fuel, t, hSetupRun, hSetupReady, hSetupCode, hSetupEffect⟩ :=
      second_loop_setup boundary hOutside v hBranchReady hCode₂ hEntry
    refine ⟨2 + fuel, t, (hCmpRun.trans hBranchRun).trans hSetupRun,
      hSetupReady, hSetupCode, ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa only [secondLoopSetupEffect, decide_eq_true hlt, Bool.true_eq, ite_true]
        using hSetupEffect.rip
    · intro _
      exact hSetupEffect.writes
    · exact (hBefore.trans hSetupEffect.agrees).mono (by
        simp [secondLoopSetupEffect, Effect.components])
  · refine ⟨2, v, hCmpRun.trans hBranchRun, hBranchReady, hCode₂, ?_⟩
    refine ⟨?_, ?_, hBefore.mono (by simp)⟩
    · simpa only [ite_eq_right hlt, decide_eq_false hlt, Bool.false_eq_true, ite_false] using hPc
    · simp only [decide_eq_true_eq]
      exact fun h ↦ (hlt h).elim

end Md5.Proofs.NewEntries.Reset
