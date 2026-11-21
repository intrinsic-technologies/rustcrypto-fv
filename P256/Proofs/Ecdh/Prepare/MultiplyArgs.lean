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

def multiplyArgsBytes : List UInt8 :=
  [72, 141, 188, 36, 152, 0, 0, 0, 186, 1, 0, 0, 0, 65, 184, 1, 0, 0, 0, 76, 137, 254, 76, 137, 241]

def multiplyArgsEffect (s : RamState) : Effect :=
  { rip := 0x10033b
    writes := [⟨(Operand.reg 7 : Operand 64), stackPtr s + 152⟩,
      ⟨(Operand.reg 2 : Operand 64), 1⟩,
      ⟨(Operand.reg 8 : Operand 64), 1⟩,
      ⟨(Operand.reg 6 : Operand 64), (Operand.reg 15 : Operand 64).read s⟩,
      ⟨(Operand.reg 1 : Operand 64), (Operand.reg 14 : Operand 64).read s⟩] }

theorem multiplyArgs_block [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x100322)
      (codeRange 0x100322 multiplyArgsBytes) (Effect.post multiplyArgsEffect) := by
  advance_begin (lea_r64_effect_step 0x100322 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 152)) (by decide +kernel) rfl rfl)
  case next => intro _ _; exact boundary_ne_program hout (inProgram_of_textOffset 0x32a (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10032a 0xba (by decide) 1)
  case sub => exact codeRange_slice_subset 0x100322 multiplyArgsBytes 8 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x32f (by decide))⟩
  advance_then (mov_r32_imm32_rex_effect_step 0x10032f 0x41 0xb8 (by simp [RexNoWPrefix]) (by decide) 1)
  case sub => exact codeRange_slice_subset 0x100322 multiplyArgsBytes 13 6
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x335 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x100335 0x4c 0xfe (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x100322 multiplyArgsBytes 19 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x338 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x100338 0x4c 0xf1 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x100322 multiplyArgsBytes 22 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x33b (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [multiplyArgsEffect, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [multiplyArgsEffect, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [multiplyArgsEffect, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [multiplyArgsEffect, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)

theorem multiplyArgs_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x100000 32 32 3464)
    (state : ScalarFrame.FrameState s t 32 3464 2056) (rip : t.RIP = 0x100322) :
    ∃ fuel u, Advances boundary fuel t u ∧ ScalarFrame.FrameState s u 32 3464 2056 ∧
      (multiplyArgsEffect t).Holds t u := by
  obtain ⟨fuel,u,run,ready,_,effect⟩ := multiplyArgs_block boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x322 multiplyArgsBytes
      (by decide) (by decide +kernel)) rip
  refine ⟨fuel,u,run,state.after_registers ready effect.agrees ?_ ?_,effect⟩
  · simp [multiplyArgsEffect,Effect.components,Component.Covers]
  · simp [multiplyArgsEffect,Effect.components]

end P256.Proofs.Ecdh.Prepare
