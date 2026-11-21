import P256.Proofs.Projective.Add.Combinations.Setup

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)

namespace P256.Proofs.Projective.Add.Combinations

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def XXMinusBytes : List UInt8 :=
  [0x4c, 0x8d, 0xac, 0x24, 0xc8, 0x0, 0x0, 0x0, 0x4c, 0x89, 0xef, 0x4c, 0x89, 0xfe, 0x48, 0x89, 0xea]

def XXMinusEffect (s : RamState) : Effect :=
  { rip := 0x105aeb
    writes := [
      ⟨(Operand.reg 2 : Operand 64), (Operand.reg 5 : Operand 64).read s⟩,
      ⟨(Operand.reg 6 : Operand 64), (Operand.reg 15 : Operand 64).read s⟩,
      ⟨(Operand.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s + 200⟩,
      ⟨(Operand.reg 13 : Operand 64), (Operand.reg 4 : Operand 64).read s + 200⟩] }

theorem XXMinus_block [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (SetupPre 0x105ada) (codeRange 0x105ada XXMinusBytes) (Effect.post XXMinusEffect) := by
  advance_begin (lea_r64_effect_step 0x105ada 0x4c (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d32 200)) (by decide) rfl rfl)
  case next => intro s hP; exact boundary_ne_program hout (inProgram_of_textOffset 0x5ae2 (by decide))
  advance_then (mov_r64_r64_effect_step 0x105ae2 0x4c 0xef (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x105ada XXMinusBytes 8 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x5ae5 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x105ae5 0x4c 0xfe (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x105ada XXMinusBytes 11 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x5ae8 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x105ae8 0x48 0xea (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x105ada XXMinusBytes 14 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x5aeb (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [XXMinusEffect]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [XXMinusEffect]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [XXMinusEffect]
  · x86_norm [XXMinusEffect]
    all_goals (repeat first | constructor | rfl)

end P256.Proofs.Projective.Add.Combinations
