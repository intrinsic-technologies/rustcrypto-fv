import P256.Proofs.Projective.Add.Combinations.Setup

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)

namespace P256.Proofs.Projective.Add.Combinations

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def DoubleBXZMinusBytes : List UInt8 :=
  [0x4c, 0x8d, 0x6c, 0x24, 0x28, 0x4c, 0x89, 0xef, 0x4c, 0x89, 0xf6]

def DoubleBXZMinusEffect (s : RamState) : Effect :=
  { rip := 0x105a37
    writes := [
      ⟨(Operand.reg 6 : Operand 64), (Operand.reg 14 : Operand 64).read s⟩,
      ⟨(Operand.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s + 40⟩,
      ⟨(Operand.reg 13 : Operand 64), (Operand.reg 4 : Operand 64).read s + 40⟩] }

theorem DoubleBXZMinus_block [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (SetupPre 0x105a2c) (codeRange 0x105a2c DoubleBXZMinusBytes) (Effect.post DoubleBXZMinusEffect) := by
  advance_begin (lea_r64_effect_step 0x105a2c 0x4c (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d8 40)) (by decide) rfl rfl)
  case next => intro s hP; exact boundary_ne_program hout (inProgram_of_textOffset 0x5a31 (by decide))
  advance_then (mov_r64_r64_effect_step 0x105a31 0x4c 0xef (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x105a2c DoubleBXZMinusBytes 5 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x5a34 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x105a34 0x4c 0xf6 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x105a2c DoubleBXZMinusBytes 8 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x5a37 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [DoubleBXZMinusEffect]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [DoubleBXZMinusEffect]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [DoubleBXZMinusEffect]
  · x86_norm [DoubleBXZMinusEffect]
    all_goals (repeat first | constructor | rfl)

end P256.Proofs.Projective.Add.Combinations
