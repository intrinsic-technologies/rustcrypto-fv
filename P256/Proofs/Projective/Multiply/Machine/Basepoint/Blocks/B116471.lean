import P256.Proofs.Program.Code
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Projective.Multiply.Machine.Basepoint.Blocks

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs

def b116471Bytes : List UInt8 :=
  [73, 137, 247, 72, 137, 251, 72, 141, 188, 36, 8, 1, 0, 0, 185, 12, 0, 0, 0, 72, 199, 198, 200, 42, 32, 0]

def b116471Effect (s : RamState) : Effect :=
  { rip := 0x10e71b
    writes := [⟨(Operand.reg 15 : Operand 64), (Operand.reg 6 : Operand 64).read s⟩,
      ⟨(Operand.reg 3 : Operand 64), (Operand.reg 7 : Operand 64).read s⟩,
      ⟨(Operand.reg 7 : Operand 64), stackPtr s + 264⟩,
      ⟨(Operand.reg 1 : Operand 64), 12⟩,
      ⟨(Operand.reg 6 : Operand 64), 2108104⟩] }

theorem b116471_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10e701)
      (codeRange 0x10e701 b116471Bytes) (Effect.post b116471Effect) := by
  advance_begin (mov_r64_r64_effect_step 0x10e701 0x49 0xf7 (by simp [RexWPrefix]) rfl)
  case next => intro _ _; exact boundary_ne_program hout (inProgram_of_textOffset 0xe704 (by decide))
  advance_then (mov_r64_r64_effect_step 0x10e704 0x48 0xfb (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10e701 b116471Bytes 3 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xe707 (by decide))⟩
  advance_then (lea_r64_effect_step 0x10e707 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 264)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10e701 b116471Bytes 6 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xe70f (by decide))⟩
  advance_then (mov_r32_imm32_effect_step 0x10e70f 0xb9 (by decide) 12)
  case sub => exact codeRange_slice_subset 0x10e701 b116471Bytes 14 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xe714 (by decide))⟩
  advance_then (mov_r64_imm32_effect_step 0x10e714 0x48 0xc6 (by simp [RexWPrefix]) rfl rfl 2108104)
  case sub => exact codeRange_slice_subset 0x10e701 b116471Bytes 19 7
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xe71b (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [b116471Effect, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [b116471Effect, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [b116471Effect, BitVec.add_zero]
  · x86_norm [b116471Effect, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)

end P256.Proofs.Projective.Multiply.Machine.Basepoint.Blocks
