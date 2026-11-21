import P256.Proofs.Program.ScalarFrame.State
import P256.Proofs.Program.Code
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Projective.Multiply.Machine.Basepoint.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program

def multiplyArgsBytes : List UInt8 :=
  [72, 141, 124, 36, 64, 186, 1, 0, 0, 0, 65, 184, 1, 0, 0, 0, 76, 137, 254, 76, 137, 241]

def multiplyArgsEffect (s : RamState) : Effect :=
  { rip := 0x10e94e
    writes := [⟨(Operand.reg 7 : Operand 64), stackPtr s + 64⟩,
      ⟨(Operand.reg 2 : Operand 64), 1⟩,
      ⟨(Operand.reg 8 : Operand 64), 1⟩,
      ⟨(Operand.reg 6 : Operand 64), (Operand.reg 15 : Operand 64).read s⟩,
      ⟨(Operand.reg 1 : Operand 64), (Operand.reg 14 : Operand 64).read s⟩] }

theorem multiplyArgs_block [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10e938)
      (codeRange 0x10e938 multiplyArgsBytes) (Effect.post multiplyArgsEffect) := by
  advance_begin (lea_r64_effect_step 0x10e938 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 64)) (by decide +kernel) rfl rfl)
  case next => intro _ _; exact boundary_ne_program hout (inProgram_of_textOffset 0xe93d (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10e93d 0xba (by decide) 1)
  case sub => exact codeRange_slice_subset 0x10e938 multiplyArgsBytes 5 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xe942 (by decide))⟩
  advance_then (mov_r32_imm32_rex_effect_step 0x10e942 0x41 0xb8 (by simp [RexNoWPrefix]) (by decide) 1)
  case sub => exact codeRange_slice_subset 0x10e938 multiplyArgsBytes 10 6
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xe948 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10e948 0x4c 0xfe (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10e938 multiplyArgsBytes 16 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xe94b (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10e94b 0x4c 0xf1 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10e938 multiplyArgsBytes 19 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xe94e (by decide))⟩
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
    (pre : CalleePre s boundary 0x10e6f0 32 65 3352)
    (state : ScalarFrame.FrameState s t 65 3352 1944) (rip : t.RIP = 0x10e938) :
    ∃ fuel u, Advances boundary fuel t u ∧ ScalarFrame.FrameState s u 65 3352 1944 ∧
      (multiplyArgsEffect t).Holds t u := by
  obtain ⟨fuel,u,run,ready,_,effect⟩ := multiplyArgs_block boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xe938 multiplyArgsBytes
      (by decide) (by decide +kernel)) rip
  refine ⟨fuel,u,run,state.after_registers ready effect.agrees ?_ ?_,effect⟩
  · simp [multiplyArgsEffect,Effect.components,Component.Covers]
  · simp [multiplyArgsEffect,Effect.components]

end P256.Proofs.Projective.Multiply.Machine.Basepoint.Finish
