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

def b114e50Bytes : List UInt8 :=
  [185, 12, 0, 0, 0, 76, 137, 239, 72, 137, 238]

def b114e50Effect (s : RamState) : Effect :=
  { rip := 0x10020b
    writes := [⟨(Operand.reg 1 : Operand 64), 12⟩,
      ⟨(Operand.reg 7 : Operand 64), (Operand.reg 13 : Operand 64).read s⟩,
      ⟨(Operand.reg 6 : Operand 64), (Operand.reg 5 : Operand 64).read s⟩] }

theorem b114e50_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x100200)
      (codeRange 0x100200 b114e50Bytes) (Effect.post b114e50Effect) := by
  advance_begin (mov_r32_imm32_effect_step 0x100200 0xb9 (by decide) 12)
  case next => intro _ _; exact boundary_ne_program hout (inProgram_of_textOffset 0x205 (by decide))
  advance_then (mov_r64_r64_effect_step 0x100205 0x4c 0xef (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x100200 b114e50Bytes 5 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x208 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x100208 0x48 0xee (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x100200 b114e50Bytes 8 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x20b (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [b114e50Effect, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [b114e50Effect, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [b114e50Effect, BitVec.add_zero]
  · x86_norm [b114e50Effect, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)

end P256.Proofs.Ecdh.Table.Blocks
