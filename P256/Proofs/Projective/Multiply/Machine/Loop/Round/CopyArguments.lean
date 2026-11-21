import P256.Proofs.Projective.Multiply.Machine.Loop.Initial.Setup
import X86Proofs.Instructions.Dec.Generated.R.Triple
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Projective.Multiply.Machine.Loop.Round

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs


def copyArgumentsBytes : List UInt8 :=
  [185, 12, 0, 0, 0, 72, 137, 199, 76, 137, 238]

def copyArgumentsEffect (s : RamState) : Effect :=
  { rip := 0x10338b
    writes := [⟨(Operand.reg 1 : Operand 64), 12⟩,
      ⟨(Operand.reg 7 : Operand 64), s.regValue .rax⟩,
      ⟨(Operand.reg 6 : Operand 64), s.regValue .r13⟩] }

theorem copyArguments_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x103380) (codeRange 0x103380 copyArgumentsBytes)
      (Effect.post copyArgumentsEffect) := by
  advance_begin (mov_r32_imm32_effect_step 0x103380 0xb9 (by decide) 12)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x3385 (by decide))
  advance_then (mov_r64_r64_effect_step 0x103385 0x48 0xc7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x103380 copyArgumentsBytes 5 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x3388 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x103388 0x4c 0xee (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x103380 copyArgumentsBytes 8 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x338b (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [copyArgumentsEffect, BitVec.shiftLeft_zero, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [copyArgumentsEffect, BitVec.shiftLeft_zero, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [copyArgumentsEffect, BitVec.shiftLeft_zero, BitVec.add_zero]
  · x86_norm [copyArgumentsEffect, BitVec.shiftLeft_zero, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)

end P256.Proofs.Projective.Multiply.Machine.Loop.Round
