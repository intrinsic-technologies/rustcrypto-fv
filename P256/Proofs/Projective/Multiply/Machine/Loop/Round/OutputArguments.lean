import P256.Proofs.Projective.Multiply.Machine.Loop.Initial.Setup
import X86Proofs.Instructions.Dec.Generated.R.Triple
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Projective.Multiply.Machine.Loop.Round

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs


def outputArgumentsBytes : List UInt8 :=
  [72, 137, 232, 185, 12, 0, 0, 0, 76, 137, 239, 72, 137, 238]

def outputArgumentsEffect (s : RamState) : Effect :=
  { rip := 0x1033bb
    writes := [⟨(Operand.reg 0 : Operand 64), s.regValue .rbp⟩,
      ⟨(Operand.reg 1 : Operand 64), 12⟩,
      ⟨(Operand.reg 7 : Operand 64), s.regValue .r13⟩,
      ⟨(Operand.reg 6 : Operand 64), s.regValue .rbp⟩] }

theorem outputArguments_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1033ad) (codeRange 0x1033ad outputArgumentsBytes)
      (Effect.post outputArgumentsEffect) := by
  advance_begin (mov_r64_r64_effect_step 0x1033ad 0x48 0xe8 (by simp [RexWPrefix]) rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x33b0 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x1033b0 0xb9 (by decide) 12)
  case sub => exact codeRange_slice_subset 0x1033ad outputArgumentsBytes 3 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x33b5 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x1033b5 0x4c 0xef (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1033ad outputArgumentsBytes 8 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x33b8 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x1033b8 0x48 0xee (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1033ad outputArgumentsBytes 11 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x33bb (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [outputArgumentsEffect, BitVec.shiftLeft_zero, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [outputArgumentsEffect, BitVec.shiftLeft_zero, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [outputArgumentsEffect, BitVec.shiftLeft_zero, BitVec.add_zero]
  · x86_norm [outputArgumentsEffect, BitVec.shiftLeft_zero, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)

end P256.Proofs.Projective.Multiply.Machine.Loop.Round
