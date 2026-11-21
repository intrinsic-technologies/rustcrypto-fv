import P256.Proofs.Program.Code
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Ecdh.Table.Blocks

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs

def b114f2fBytes : List UInt8 :=
  [185, 12, 0, 0, 0, 72, 141, 188, 36, 152, 6, 0, 0, 76, 137, 254]

def b114f2fEffect (s : RamState) : Effect :=
  { rip := 0x1002ef
    writes := [⟨(Operand.reg 1 : Operand 64), 12⟩,
      ⟨(Operand.reg 7 : Operand 64), stackPtr s + 1688⟩,
      ⟨(Operand.reg 6 : Operand 64), (Operand.reg 15 : Operand 64).read s⟩] }

theorem b114f2f_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1002df)
      (codeRange 0x1002df b114f2fBytes) (Effect.post b114f2fEffect) := by
  advance_begin (mov_r32_imm32_effect_step 0x1002df 0xb9 (by decide) 12)
  case next => intro _ _; exact boundary_ne_program hout (inProgram_of_textOffset 0x2e4 (by decide))
  advance_then (lea_r64_effect_step 0x1002e4 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 1688)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1002df b114f2fBytes 5 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x2ec (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x1002ec 0x4c 0xfe (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1002df b114f2fBytes 13 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x2ef (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [b114f2fEffect, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [b114f2fEffect, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [b114f2fEffect, BitVec.add_zero]
  · x86_norm [b114f2fEffect, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)

end P256.Proofs.Ecdh.Table.Blocks
