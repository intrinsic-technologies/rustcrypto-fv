import P256.Proofs.Program.ScalarFrame.State
import P256.Proofs.Program.Code
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Ecdh.Prepare

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program

def copyArgsBytes : List UInt8 :=
  [76, 141, 188, 36, 248, 0, 0, 0, 186, 0, 3, 0, 0, 76, 137, 255, 72, 141, 180, 36, 248, 3, 0, 0]

def copyArgsEffect (s : RamState) : Effect :=
  { rip := 0x10031c
    writes := [⟨(Operand.reg 15 : Operand 64), stackPtr s + 248⟩,
      ⟨(Operand.reg 2 : Operand 64), 768⟩,
      ⟨(Operand.reg 7 : Operand 64), stackPtr s + 248⟩,
      ⟨(Operand.reg 6 : Operand 64), stackPtr s + 1016⟩] }

theorem copyArgs_block [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x100304)
      (codeRange 0x100304 copyArgsBytes) (Effect.post copyArgsEffect) := by
  advance_begin (lea_r64_effect_step 0x100304 0x4c (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 248)) (by decide +kernel) rfl rfl)
  case next => intro _ _; exact boundary_ne_program hout (inProgram_of_textOffset 0x30c (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10030c 0xba (by decide) 768)
  case sub => exact codeRange_slice_subset 0x100304 copyArgsBytes 8 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x311 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x100311 0x4c 0xff (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x100304 copyArgsBytes 13 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x314 (by decide))⟩
  advance_then (lea_r64_effect_step 0x100314 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 1016)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100304 copyArgsBytes 16 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x31c (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [copyArgsEffect, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [copyArgsEffect, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [copyArgsEffect, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [copyArgsEffect, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)

theorem copyArgs_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x100000 32 32 3464)
    (state : ScalarFrame.FrameState s t 32 3464 2056) (rip : t.RIP = 0x100304) :
    ∃ fuel u, Advances boundary fuel t u ∧ ScalarFrame.FrameState s u 32 3464 2056 ∧
      (copyArgsEffect t).Holds t u := by
  obtain ⟨fuel,u,run,ready,_,effect⟩ := copyArgs_block boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x304 copyArgsBytes
      (by decide) (by decide +kernel)) rip
  refine ⟨fuel,u,run,state.after_registers ready effect.agrees ?_ ?_,effect⟩
  · simp [copyArgsEffect,Effect.components,Component.Covers]
  · simp [copyArgsEffect,Effect.components]

end P256.Proofs.Ecdh.Prepare
