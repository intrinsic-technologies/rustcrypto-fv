import P256.Proofs.Projective.Multiply.Machine.Loop.Initial.Setup

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Projective.Multiply.Machine.Loop.Initial

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs

def copyArgumentsBytes : List UInt8 :=
  [0xb9,12,0,0,0,0x4c,0x8d,0xb4,0x24,0xe8,0,0,0,
    0x4c,0x89,0xf7,0x48,0x8d,0x74,0x24,0x28]

def copyArgumentsEffect (s : RamState) : Effect :=
  { rip := 0x1032c5
    writes := [⟨(Operand.reg 1 : Operand 64), 12⟩,
      ⟨(Operand.reg 14 : Operand 64), stackPtr s + 232⟩,
      ⟨(Operand.reg 7 : Operand 64), stackPtr s + 232⟩,
      ⟨(Operand.reg 6 : Operand 64), stackPtr s + 40⟩] }

theorem copyArguments_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1032b0)
      (codeRange 0x1032b0 copyArgumentsBytes) (Effect.post copyArgumentsEffect) := by
  advance_begin (mov_r32_imm32_effect_step 0x1032b0 0xb9 (by decide) 12)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x32b5 (by decide))
  advance_then (lea_r64_effect_step 0x1032b5 0x4c (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d32 232)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1032b0 copyArgumentsBytes 5 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x32bd (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x1032bd 0x4c 0xf7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1032b0 copyArgumentsBytes 13 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x32c0 (by decide))⟩
  advance_then (lea_r64_effect_step 0x1032c0 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1032b0 copyArgumentsBytes 16 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x32c5 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [copyArgumentsEffect]
  · x86_norm [copyArgumentsEffect]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [copyArgumentsEffect]
  · x86_norm [copyArgumentsEffect]
    all_goals (repeat first | constructor | rfl)

end P256.Proofs.Projective.Multiply.Machine.Loop.Initial
