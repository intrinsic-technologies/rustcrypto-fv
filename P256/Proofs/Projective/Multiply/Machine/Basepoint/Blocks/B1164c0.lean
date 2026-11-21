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

def b1164c0Bytes : List UInt8 :=
  [76, 137, 239, 72, 199, 198, 200, 42, 32, 0]

def b1164c0Effect (s : RamState) : Effect :=
  { rip := 0x10e75a
    writes := [⟨(Operand.reg 7 : Operand 64), (Operand.reg 13 : Operand 64).read s⟩,
      ⟨(Operand.reg 6 : Operand 64), 2108104⟩] }

theorem b1164c0_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10e750)
      (codeRange 0x10e750 b1164c0Bytes) (Effect.post b1164c0Effect) := by
  advance_begin (mov_r64_r64_effect_step 0x10e750 0x4c 0xef (by simp [RexWPrefix]) rfl)
  case next => intro _ _; exact boundary_ne_program hout (inProgram_of_textOffset 0xe753 (by decide))
  advance_then (mov_r64_imm32_effect_step 0x10e753 0x48 0xc6 (by simp [RexWPrefix]) rfl rfl 2108104)
  case sub => exact codeRange_slice_subset 0x10e750 b1164c0Bytes 3 7
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xe75a (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [b1164c0Effect, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [b1164c0Effect, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [b1164c0Effect, BitVec.add_zero]
  · x86_norm [b1164c0Effect, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)

end P256.Proofs.Projective.Multiply.Machine.Basepoint.Blocks
