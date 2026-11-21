import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple
import P256.Proofs.Common.Curve.LinearCombination.Loop.Instructions.Scale
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program
open P256.Spec.Program.Routines

namespace P256.Proofs.Verifying.Combination.Loop.Multi.Selection

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Curve.LinearCombination.Loop.Instructions

attribute [local x86_compose] addR64Imm32Effect

def positiveStride (s : RamState) : BitVec 64 :=
  (((s.regValue .rdi + (s.regValue .rdi <<< 1)).setWidth 32) <<< 5).setWidth 64

def positiveSetupBytes : List UInt8 :=
  [0x48, 0x8d, 0x34, 0x7f, 0xc1, 0xe6, 0x5, 0x48, 0x1, 0xee, 0xb9, 0xc, 0, 0, 0, 0x4c, 0x89, 0xff]

def positiveSetupEffect (s : RamState) : Effect :=
  { rip := 0x10f2fc
    writes := [⟨(Operand.reg 6 : Operand 64), positiveStride s + s.regValue .rbp⟩,
      ⟨(Operand.reg 1 : Operand 64), 12⟩,
      ⟨(Operand.reg 7 : Operand 64), s.regValue .r15⟩]
    flags := some (.ofStatusFlags (addSpec (positiveStride s) (s.regValue .rbp)).2) }

theorem positiveSetup_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10f2ea)
      (codeRange 0x10f2ea positiveSetupBytes) (Effect.post positiveSetupEffect) := by
  advance_begin (lea_r64_effect_step 0x10f2ea 0x48 (by simp [RexWPrefix]) 6 (.sib 7 (some 7) 1 .none) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0xf2ee (by decide))
  advance_then (shl_r32_imm8_effect_step 0x10f2ee 0xe6 5 rfl rfl)
  case loc => exact shlR32Effect_local _ _ _ _ (by decide)
  case sub => exact codeRange_slice_subset 0x10f2ea positiveSetupBytes 4 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xf2f1 (by decide))⟩
  advance_then (add_r64_r64_effect_step 0x10f2f1 0x48 0xee (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10f2ea positiveSetupBytes 7 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xf2f4 (by decide))⟩
  advance_then (mov_r32_imm32_effect_step 0x10f2f4 0xb9 (by decide) 12)
  case sub => exact codeRange_slice_subset 0x10f2ea positiveSetupBytes 10 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xf2f9 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10f2f9 0x4c 0xff (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10f2ea positiveSetupBytes 15 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xf2fc (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [positiveSetupEffect, positiveStride, BitVec.add_zero, BitVec.shiftLeft_zero]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [positiveSetupEffect, positiveStride, BitVec.add_zero, BitVec.shiftLeft_zero]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [positiveSetupEffect, positiveStride, BitVec.add_zero, BitVec.shiftLeft_zero]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [positiveSetupEffect, positiveStride, BitVec.add_zero, BitVec.shiftLeft_zero]
    all_goals (repeat first | constructor | rfl)

end P256.Proofs.Verifying.Combination.Loop.Multi.Selection
