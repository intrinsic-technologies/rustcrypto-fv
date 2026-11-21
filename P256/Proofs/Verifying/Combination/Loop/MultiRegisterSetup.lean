import P256.Proofs.Verifying.Combination.Loop.MultiLength
import X86Proofs.Instructions.Xor.Generated.RR.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

def registerSetupBytes : List UInt8 :=
  [0x45,0x31,0xf6,0x4c,0x8d,0xbc,0x24,8,1,0,0,0xeb,0x15]

def registerSetupEffect (s : RamState) : Effect :=
  { rip := 0x10f174
    writes := [⟨(.reg 14 : Operand 64), 0⟩,
      ⟨(.reg 15 : Operand 64), stackPtr s + 264⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem registerSetup_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10f152)
      (codeRange 0x10f152 registerSetupBytes) (Effect.post registerSetupEffect) := by
  advance_begin (xor_r32_r32_rex_effect_step 0x10f152 0x45 0xf6 (by simp [RexNoWPrefix]) rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0xf155 (by decide))
  advance_then (lea_r64_effect_step 0x10f155 0x4c (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d32 264)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f152 registerSetupBytes 3 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xf15d (by decide))⟩
  advance_then (jmp_rel8_effect_step 0x10f15d 0x15 (by decide +kernel))
  case sub => exact codeRange_slice_subset 0x10f152 registerSetupBytes 11 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xf174 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [registerSetupEffect]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [registerSetupEffect]
    all_goals (repeat first | constructor | rfl)
    change 0#64 = ((s.regValue .r14).setWidth 32 ^^^ (s.regValue .r14).setWidth 32).setWidth 64
    rw [BitVec.xor_self, BitVec.setWidth_zero]
  · intro i; cases i <;> x86_norm [registerSetupEffect]
  · x86_norm [registerSetupEffect]
    all_goals (repeat first | constructor | rfl)

theorem initialize_registers [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64} (pre : MultiPre s boundary tables digits)
    (state : State s t) (rip : t.RIP = 0x10f152) :
    ∃ fuel w, Advances boundary fuel t w ∧ State s w ∧ w.RIP = 0x10f174 ∧
      w.regValue .r14 = 0 ∧ w.regValue .r15 = stackPtr s - 144 ∧
      AgreesExcept [.reg 14, .reg 15, .flags, .rip] t w := by
  obtain ⟨fuel, w, run, ready, _, effect⟩ := registerSetup_correct boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xf152 registerSetupBytes
      (by decide) (by decide +kernel)) rip
  have frame : AgreesExcept [.reg 14, .reg 15, .flags, .rip] t w := effect.agrees
  exact ⟨fuel, w, run,
    state.after_registers ready frame (by simp [Component.Covers]) (by simp), effect.rip,
    effect.writes.1,
    effect.writes.2.trans (scalar_stack_address state.rsp (offset := 264) (by decide) (by decide)), frame⟩

end P256.Proofs.Verifying.Combination.Loop.Multi
