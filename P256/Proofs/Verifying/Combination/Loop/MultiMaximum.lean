import P256.Proofs.Verifying.Combination.Loop.MultiRemaining
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

def maximumSetupBytes : List UInt8 :=
  [0x48,0x8b,0x4c,0x24,8,0x4c,0x8d,0x51,0xfe,0x89,0xf1,0x83,0xe1,3,0x49,0x83,0xfa,3]

def maximumSetupEffect (s : RamState) : Effect :=
  let remaining := memLoad s.external (stackPtr s + 8) 64 + (-2#64)
  { rip := 0x10f02c
    writes := [⟨(.reg 10 : Operand 64), remaining⟩,
      ⟨(.reg 1 : Operand 64), ((s.regValue .rsi).setWidth 32 &&& 3#32).setWidth 64⟩]
    flags := some (.ofStatusFlags (cmpSpec remaining 3)) }

theorem maximumSetup_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (LoadPre 0x10f01a (fun s => stackPtr s + 8) 8)
      (codeRange 0x10f01a maximumSetupBytes) (Effect.post maximumSetupEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x10f01a 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0xf01f (by decide))
  advance_then (lea_r64_effect_step 0x10f01f 0x4c (by simp [RexWPrefix]) 2 (.base 1 (.d8 0xfe)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f01a maximumSetupBytes 5 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xf023 (by decide))⟩
  advance_then (mov_r32_r32_effect_step 0x10f023 0xf1 rfl)
  case sub => exact codeRange_slice_subset 0x10f01a maximumSetupBytes 9 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xf025 (by decide))⟩
  advance_then (and_r32_imm8_effect_step 0x10f025 0xe1 3 rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f01a maximumSetupBytes 11 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xf028 (by decide))⟩
  advance_then (cmp_r64_imm8_effect_step 0x10f028 0x49 0xfa 3 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f01a maximumSetupBytes 14 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xf02c (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [maximumSetupEffect]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [maximumSetupEffect]
    all_goals (repeat first | constructor | rfl)
    rw [BitVec.setWidth_setWidth_of_le _ (by decide)]
    rfl
  · intro i; cases i <;> x86_norm [maximumSetupEffect] <;> rfl
  · x86_norm [maximumSetupEffect]
    all_goals (repeat first | constructor | rfl)

theorem maximum_setup [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64} (pre : MultiPre s boundary tables digits)
    (state : State s t) (rip : t.RIP = 0x10f01a)
    (remaining : t.regValue .rsi = 1) (count : memLoad t.external (stackPtr s - 400) 64 = 2) :
    ∃ fuel w, Advances boundary fuel t w ∧ State s w ∧ w.RIP = 0x10f02c ∧
      w.regValue .r10 = 0 ∧ w.regValue .rcx = 1 ∧
      (StatusFlags.ofRFLAGS w.RFLAGS).CF = true ∧
      AgreesExcept [.reg 10, .reg 1, .flags, .rip] t w := by
  obtain ⟨fuel, w, run, ready, _, effect⟩ := maximumSetup_correct boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xf01a maximumSetupBytes
      (by decide) (by decide +kernel))
    ⟨rip, stack_readable pre.toCalleePre state (offset := 8) (by decide) (by decide)⟩
  have frame : AgreesExcept [.reg 10, .reg 1, .flags, .rip] t w := effect.agrees
  have addr : stackPtr t + 8 = stackPtr s - 400 :=
    scalar_stack_address state.rsp (offset := 8) (by decide) (by decide)
  refine ⟨fuel, w, run,
    state.after_registers ready frame (by simp [Component.Covers]) (by simp), effect.rip,
    ?_, ?_, ?_, frame⟩
  · have h := effect.writes.1
    change w.regValue .r10 = memLoad t.external (stackPtr t + 8) 64 + (-2#64) at h
    rw [addr, count] at h
    exact h.trans (by decide +kernel)
  · have h := effect.writes.2
    change w.regValue .rcx = ((t.regValue .rsi).setWidth 32 &&& 3#32).setWidth 64 at h
    rw [remaining] at h
    exact h.trans (by decide +kernel)
  · have h := effect.flags.1
    change (StatusFlags.ofRFLAGS w.RFLAGS).CF =
      (cmpSpec (memLoad t.external (stackPtr t + 8) 64 + (-2#64)) 3).CF at h
    rw [addr, count] at h
    exact h.trans (by decide +kernel)

theorem short_maximum [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64} (pre : MultiPre s boundary tables digits)
    (state : State s t) (rip : t.RIP = 0x10f02c)
    (cf : (StatusFlags.ofRFLAGS t.RFLAGS).CF = true) :
    ∃ w, Advances boundary 3 t w ∧ State s w ∧ w.RIP = 0x10f0e3 ∧
      w.regValue .rdi = 0 ∧ AgreesExcept [.reg 7, .flags, .rip] t w := by
  have target : (jccEffect 0x10f02c 2 3 ((0x20 : BitVec 8).signExtend 64) t).rip = 0x10f02e := by
    simp only [jccEffect, branchEffect, condHolds, cf]
    rfl
  obtain ⟨a, runA, readyA, effectA⟩ :=
    (jcc_rel8_effect_step 0x10f02c 3 0x20).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0xf02c _
        (by decide) (by decide +kernel))
      ⟨rip, by intro h; decide +kernel⟩
      (by
        rw [target]
        exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf02e (by decide)))
  have frameA : AgreesExcept [.rip] t a := effectA.agrees
  have stateA := state.after_registers readyA frameA (by simp [Component.Covers]) (by simp)
  obtain ⟨b, runB, readyB, effectB⟩ :=
    (xor_r32_r32_effect_step 0x10f02e 0xff rfl).advances readyA
      (programText_slice (programLoaded_codeIn stateA.loaded) 0xf02e _
        (by decide) (by decide +kernel)) (effectA.rip.trans target)
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf030 (by decide)))
  have frameB : AgreesExcept [.reg 7, .flags, .rip] a b := effectB.agrees
  have stateB := stateA.after_registers readyB frameB (by simp [Component.Covers]) (by simp)
  have zeroB : b.regValue .rdi = 0 := by
    have h := effectB.writes
    change b.regValue .rdi = ((a.regValue .rdi).setWidth 32 ^^^
      (a.regValue .rdi).setWidth 32).setWidth 64 at h
    rw [BitVec.xor_self, BitVec.setWidth_zero] at h
    exact h.trans (by decide +kernel)
  obtain ⟨w, runW, readyW, effectW⟩ :=
    (jmp_rel32_effect_step 0x10f030 0xae (by decide +kernel)).advances readyB
      (programText_slice (programLoaded_codeIn stateB.loaded) 0xf030 _
        (by decide) (by decide +kernel)) effectB.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf0e3 (by decide)))
  have frameW : AgreesExcept [.rip] b w := effectW.agrees
  have frame : AgreesExcept [.reg 7, .flags, .rip] t w :=
    ((frameA.trans frameB).trans frameW).mono (by simp)
  exact ⟨w, (runA.trans runB).trans runW,
    state.after_registers readyW frame (by simp [Component.Covers]) (by simp), effectW.rip,
    (frameW.read (n := 64) (r := 7) (by simp)).trans zeroB, frame⟩

end P256.Proofs.Verifying.Combination.Loop.Multi
