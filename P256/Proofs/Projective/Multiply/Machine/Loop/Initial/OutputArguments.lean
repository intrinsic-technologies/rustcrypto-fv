import P256.Proofs.Projective.Multiply.Machine.Loop.Initial.Setup

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Projective.Multiply.Machine.Loop.Initial

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs

def outputArgumentsBytes : List UInt8 :=
  [0x49,0x89,0xe9,0xb9,12,0,0,0,0x48,0x8d,0x7c,0x24,0x28,0x4c,0x89,0xf6]

def outputArgumentsEffect (s : RamState) : Effect :=
  { rip := 0x1032ff
    writes := [⟨(Operand.reg 9 : Operand 64), s.regValue .rbp⟩,
      ⟨(Operand.reg 1 : Operand 64), 12⟩,
      ⟨(Operand.reg 7 : Operand 64), stackPtr s + 40⟩,
      ⟨(Operand.reg 6 : Operand 64), s.regValue .r14⟩] }

theorem outputArguments_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1032ef)
      (codeRange 0x1032ef outputArgumentsBytes) (Effect.post outputArgumentsEffect) := by
  advance_begin (mov_r64_r64_effect_step 0x1032ef 0x49 0xe9 (by simp [RexWPrefix]) rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x32f2 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x1032f2 0xb9 (by decide) 12)
  case sub => exact codeRange_slice_subset 0x1032ef outputArgumentsBytes 3 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x32f7 (by decide))⟩
  advance_then (lea_r64_effect_step 0x1032f7 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1032ef outputArgumentsBytes 8 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x32fc (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x1032fc 0x4c 0xf6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1032ef outputArgumentsBytes 13 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x32ff (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [outputArgumentsEffect]
  · x86_norm [outputArgumentsEffect]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [outputArgumentsEffect]
  · x86_norm [outputArgumentsEffect]
    all_goals (repeat first | constructor | rfl)

end P256.Proofs.Projective.Multiply.Machine.Loop.Initial
