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

def radixArgsBytes : List UInt8 :=
  [76, 141, 180, 36, 160, 0, 0, 0, 76, 137, 247, 76, 137, 254]

def radixArgsEffect (s : RamState) : Effect :=
  { rip := 0x10e915
    writes := [⟨(Operand.reg 14 : Operand 64), stackPtr s + 160⟩,
      ⟨(Operand.reg 7 : Operand 64), stackPtr s + 160⟩,
      ⟨(Operand.reg 6 : Operand 64), (Operand.reg 15 : Operand 64).read s⟩] }

theorem radixArgs_block [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10e907)
      (codeRange 0x10e907 radixArgsBytes) (Effect.post radixArgsEffect) := by
  advance_begin (lea_r64_effect_step 0x10e907 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 160)) (by decide +kernel) rfl rfl)
  case next => intro _ _; exact boundary_ne_program hout (inProgram_of_textOffset 0xe90f (by decide))
  advance_then (mov_r64_r64_effect_step 0x10e90f 0x4c 0xf7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10e907 radixArgsBytes 8 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xe912 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10e912 0x4c 0xfe (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10e907 radixArgsBytes 11 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xe915 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [radixArgsEffect, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [radixArgsEffect, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [radixArgsEffect, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [radixArgsEffect, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)

theorem radixArgs_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10e6f0 32 65 3352)
    (state : ScalarFrame.FrameState s t 65 3352 1944) (rip : t.RIP = 0x10e907) :
    ∃ fuel u, Advances boundary fuel t u ∧ ScalarFrame.FrameState s u 65 3352 1944 ∧
      (radixArgsEffect t).Holds t u := by
  obtain ⟨fuel,u,run,ready,_,effect⟩ := radixArgs_block boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xe907 radixArgsBytes
      (by decide) (by decide +kernel)) rip
  refine ⟨fuel,u,run,state.after_registers ready effect.agrees ?_ ?_,effect⟩
  · simp [radixArgsEffect,Effect.components,Component.Covers]
  · simp [radixArgsEffect,Effect.components]

end P256.Proofs.Projective.Multiply.Machine.Basepoint.Finish
