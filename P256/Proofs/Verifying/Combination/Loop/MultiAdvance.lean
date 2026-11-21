import P256.Proofs.Verifying.Combination.Loop.MultiLength
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import X86Proofs.Instructions.Dec.Generated.R.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

def advanceBytes : List UInt8 :=
  [0x49,0x81,0xc5,0x10,1,0,0,0x48,0x81,0xc5,0,3,0,0,0x49,0xff,0xcc]

def advanceEffect (s : RamState) : Effect :=
  { rip := 0x10f2c9
    writes := [⟨(.reg 13 : Operand 64), s.regValue .r13 + 272⟩,
      ⟨(.reg 5 : Operand 64), s.regValue .rbp + 768⟩,
      ⟨(.reg 12 : Operand 64), s.regValue .r12 - 1⟩]
    flags := some ⟨none, none, none, some (s.regValue .r12 - 1 == 0), none, none⟩ }

theorem advance_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10f2b8)
      (codeRange 0x10f2b8 advanceBytes) (Effect.post advanceEffect) := by
  advance_begin (add_r64_imm32_effect_step 0x10f2b8 0x49 0xc5 272 (by simp [RexWPrefix]) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0xf2bf (by decide))
  advance_then (add_r64_imm32_effect_step 0x10f2bf 0x48 0xc5 768 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f2b8 advanceBytes 7 7
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xf2c6 (by decide))⟩
  advance_then (dec_r64_effect_step 0x10f2c6 0x49 0xcc (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f2b8 advanceBytes 14 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xf2c9 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [advanceEffect]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [advanceEffect]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [advanceEffect] <;> rfl
  · x86_norm [advanceEffect]
    all_goals (repeat first | constructor | rfl)

theorem advance_digit [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64} (left : Bool) (pre : MultiPre s boundary tables digits)
    (state : State s t) (rip : t.RIP = 0x10f2b8)
    (remaining : t.regValue .r12 = if left then 2 else 1) :
    ∃ fuel w, Advances boundary fuel t w ∧ State s w ∧
      w.RIP = (if left then 0x10f2cf else 0x10f160) ∧
      w.regValue .r13 = t.regValue .r13 + 272 ∧
      w.regValue .rbp = t.regValue .rbp + 768 ∧
      w.regValue .r12 = (if left then 1 else 0) ∧
      AgreesExcept [.reg 13, .reg 5, .reg 12, .flags, .rip] t w := by
  obtain ⟨fuel, a, runA, readyA, _, effectA⟩ := advance_correct boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xf2b8 advanceBytes
      (by decide) (by decide +kernel)) rip
  have frameA : AgreesExcept [.reg 13, .reg 5, .reg 12, .flags, .rip] t a := effectA.agrees
  have stateA := state.after_registers readyA frameA (by simp [Component.Covers]) (by simp)
  have countA : a.regValue .r12 = (if left then 1 else 0) := by
    have h := effectA.writes.2.2
    change a.regValue .r12 = t.regValue .r12 - 1 at h
    rw [remaining] at h
    cases left <;> exact h.trans (by decide +kernel)
  have zeroA : (StatusFlags.ofRFLAGS a.RFLAGS).ZF = !left := by
    have h := effectA.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS a.RFLAGS).ZF = (t.regValue .r12 - 1 == 0) at h
    rw [remaining] at h
    cases left <;> exact h.trans (by decide +kernel)
  have target : (jccEffect 0x10f2c9 6 4 ((0xfffffe91 : BitVec 32).signExtend 64) a).rip =
      (if left then 0x10f2cf else 0x10f160) := by
    cases left <;> simp only [jccEffect, branchEffect, condHolds, zeroA] <;> rfl
  obtain ⟨w, runW, readyW, effectW⟩ :=
    (jcc_rel32_effect_step 0x10f2c9 4 0xfffffe91).advances readyA
      (programText_slice (programLoaded_codeIn stateA.loaded) 0xf2c9 _
        (by decide) (by decide +kernel))
      ⟨effectA.rip, by intro h; decide +kernel⟩
      (by
        rw [target]
        cases left
        · exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf160 (by decide))
        · exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf2cf (by decide)))
  have frameW : AgreesExcept [.rip] a w := effectW.agrees
  have frame : AgreesExcept [.reg 13, .reg 5, .reg 12, .flags, .rip] t w :=
    (frameA.trans frameW).mono (by simp)
  exact ⟨fuel+1, w, runA.trans runW,
    state.after_registers readyW frame (by simp [Component.Covers]) (by simp), effectW.rip.trans target,
    (frameW.read (n := 64) (r := 13) (by simp)).trans effectA.writes.1,
    (frameW.read (n := 64) (r := 5) (by simp)).trans effectA.writes.2.1,
    (frameW.read (n := 64) (r := 12) (by simp)).trans countA, frame⟩

end P256.Proofs.Verifying.Combination.Loop.Multi
