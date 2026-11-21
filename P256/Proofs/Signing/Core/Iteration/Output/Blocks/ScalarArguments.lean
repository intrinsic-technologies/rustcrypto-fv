import P256.Proofs.Signing.Core.Iteration.Stages
import P256.Proofs.Signing.Core.Iteration.Memory
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Instructions.Bswap
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Output.Blocks

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Program Common.Field

structure ScalarArgumentsPre (s : RamState) : Prop where
  rip : s.RIP = 0x10d3c4

def ScalarArgumentsBytes : List UInt8 :=
  [76, 141, 180, 36, 176, 1, 0, 0, 72, 141, 180, 36, 176, 0, 0, 0, 76, 137, 247]

def ScalarArgumentsEffect (s : RamState) : Effect :=
  { rip := 0x10d3d7
    writes := [⟨(.reg 14 : Operand 64), stackPtr s + 432⟩,
      ⟨(.reg 6 : Operand 64), stackPtr s + 176⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 432⟩] }

set_option maxHeartbeats 1000000 in
theorem ScalarArguments_correct [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary ScalarArgumentsPre (codeRange 0x10d3c4 ScalarArgumentsBytes) (Effect.post ScalarArgumentsEffect) := by
  advance_begin (lea_r64_effect_step 0x10d3c4 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 432)) (by decide) rfl rfl)
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0xd3cc (by decide))
  advance_then (lea_r64_effect_step 0x10d3cc 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 176)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d3c4 ScalarArgumentsBytes 8 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
    exact boundary_ne_program outside (inProgram_of_textOffset 0xd3d4 (by decide))
  advance_then (mov_r64_r64_effect_step 0x10d3d4 0x4c 0xf7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10d3c4 ScalarArgumentsBytes 16 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
    exact boundary_ne_program outside (inProgram_of_textOffset 0xd3d7 (by decide))
  advance_finish [ScalarArgumentsEffect, stackPtr, Operand.read_reg64, State.regValue, gprNumber]

end P256.Proofs.Signing.Core.Iteration.Output.Blocks
