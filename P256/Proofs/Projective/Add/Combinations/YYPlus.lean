import P256.Proofs.Projective.Add.Combinations.Setup

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)

namespace P256.Proofs.Projective.Add.Combinations

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def YYPlusBytes : List UInt8 :=
  [0x48, 0x8d, 0xbc, 0x24, 0x68, 0x1, 0x0, 0x0, 0x48, 0x8d, 0xb4, 0x24, 0xa8, 0x0, 0x0, 0x0, 0x4c, 0x89, 0xea]

def YYPlusEffect (s : RamState) : Effect :=
  { rip := 0x1058f9
    writes := [
      ⟨(Operand.reg 2 : Operand 64), (Operand.reg 13 : Operand 64).read s⟩,
      ⟨(Operand.reg 6 : Operand 64), (Operand.reg 4 : Operand 64).read s + 168⟩,
      ⟨(Operand.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s + 360⟩] }

theorem YYPlus_block [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (SetupPre 0x1058e6) (codeRange 0x1058e6 YYPlusBytes) (Effect.post YYPlusEffect) := by
  advance_begin (lea_r64_effect_step 0x1058e6 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 360)) (by decide) rfl rfl)
  case next => intro s hP; exact boundary_ne_program hout (inProgram_of_textOffset 0x58ee (by decide))
  advance_then (lea_r64_effect_step 0x1058ee 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 168)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1058e6 YYPlusBytes 8 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x58f6 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x1058f6 0x4c 0xea (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x1058e6 YYPlusBytes 16 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x58f9 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [YYPlusEffect]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [YYPlusEffect]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [YYPlusEffect]
  · x86_norm [YYPlusEffect]
    all_goals (repeat first | constructor | rfl)

end P256.Proofs.Projective.Add.Combinations
