import P256.Proofs.Projective.Add.Combinations.Setup

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)

namespace P256.Proofs.Projective.Add.Combinations

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def BXZMinusBytes : List UInt8 :=
  [0x4c, 0x8d, 0xb4, 0x24, 0xe8, 0x1, 0x0, 0x0, 0x4c, 0x89, 0xf7, 0x4c, 0x89, 0xee, 0x4c, 0x89, 0xe2]

def BXZMinusEffect (s : RamState) : Effect :=
  { rip := 0x105a27
    writes := [
      ⟨(Operand.reg 2 : Operand 64), (Operand.reg 12 : Operand 64).read s⟩,
      ⟨(Operand.reg 6 : Operand 64), (Operand.reg 13 : Operand 64).read s⟩,
      ⟨(Operand.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s + 488⟩,
      ⟨(Operand.reg 14 : Operand 64), (Operand.reg 4 : Operand 64).read s + 488⟩] }

theorem BXZMinus_block [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (SetupPre 0x105a16) (codeRange 0x105a16 BXZMinusBytes) (Effect.post BXZMinusEffect) := by
  advance_begin (lea_r64_effect_step 0x105a16 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 488)) (by decide) rfl rfl)
  case next => intro s hP; exact boundary_ne_program hout (inProgram_of_textOffset 0x5a1e (by decide))
  advance_then (mov_r64_r64_effect_step 0x105a1e 0x4c 0xf7 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x105a16 BXZMinusBytes 8 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x5a21 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x105a21 0x4c 0xee (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x105a16 BXZMinusBytes 11 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x5a24 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x105a24 0x4c 0xe2 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x105a16 BXZMinusBytes 14 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x5a27 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [BXZMinusEffect]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [BXZMinusEffect]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [BXZMinusEffect]
  · x86_norm [BXZMinusEffect]
    all_goals (repeat first | constructor | rfl)

end P256.Proofs.Projective.Add.Combinations
