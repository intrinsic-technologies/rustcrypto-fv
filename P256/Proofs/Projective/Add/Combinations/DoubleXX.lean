import P256.Proofs.Projective.Add.Combinations.Setup

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)

namespace P256.Proofs.Projective.Add.Combinations

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def DoubleXXBytes : List UInt8 :=
  [0x4c, 0x8d, 0x74, 0x24, 0x28, 0x4c, 0x89, 0xf7, 0x48, 0x8d, 0x74, 0x24, 0x48]

def DoubleXXEffect (s : RamState) : Effect :=
  { rip := 0x105a95
    writes := [
      ⟨(Operand.reg 6 : Operand 64), (Operand.reg 4 : Operand 64).read s + 72⟩,
      ⟨(Operand.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s + 40⟩,
      ⟨(Operand.reg 14 : Operand 64), (Operand.reg 4 : Operand 64).read s + 40⟩] }

theorem DoubleXX_block [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (SetupPre 0x105a88) (codeRange 0x105a88 DoubleXXBytes) (Effect.post DoubleXXEffect) := by
  advance_begin (lea_r64_effect_step 0x105a88 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 40)) (by decide) rfl rfl)
  case next => intro s hP; exact boundary_ne_program hout (inProgram_of_textOffset 0x5a8d (by decide))
  advance_then (mov_r64_r64_effect_step 0x105a8d 0x4c 0xf7 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x105a88 DoubleXXBytes 5 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x5a90 (by decide))⟩
  advance_then (lea_r64_effect_step 0x105a90 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 72)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105a88 DoubleXXBytes 8 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x5a95 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [DoubleXXEffect]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [DoubleXXEffect]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [DoubleXXEffect]
  · x86_norm [DoubleXXEffect]
    all_goals (repeat first | constructor | rfl)

end P256.Proofs.Projective.Add.Combinations
