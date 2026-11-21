import P256.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple
import P256.Proofs.Program.Code

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Sec1.Affine.Uncompressed.Output

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def selectFirstBytes : List UInt8 := [0x48,0x8d,0x7c,0x24,0x60,0x48,0x8d,0x54,0x24,0x10,0x48,0x89,0xc6,0x89,0xe9]

def selectFirstEffect (s : RamState) : Effect :=
  { rip := 0x110ca4
    writes := [⟨(.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s + 96⟩,
      ⟨(.reg 2 : Operand 64), (Operand.reg 4 : Operand 64).read s + 16⟩,
      ⟨(.reg 6 : Operand 64), (Operand.reg 0 : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), ((Operand.reg 5 : Operand 32).read s).setWidth 64⟩] }

theorem select_first_setup [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x110c95)
      (codeRange 0x110c95 selectFirstBytes) (Effect.post selectFirstEffect) := by
  advance_begin (lea_r64_effect_step 0x110c95 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 96)) (by decide) rfl rfl)
  case next => intro _ _; exact boundary_ne_program hout (inProgram_of_textOffset 0x10c9a (by decide))
  advance_then (lea_r64_effect_step 0x110c9a 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 16)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110c95 selectFirstBytes 5 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x10c9f (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x110c9f 0x48 0xc6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x110c95 selectFirstBytes 10 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x10ca2 (by decide))⟩
  advance_then (mov_r32_r32_effect_step 0x110ca2 0xe9 rfl)
  case sub => exact codeRange_slice_subset 0x110c95 selectFirstBytes 13 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x10ca4 (by decide))⟩
  advance_finish [selectFirstEffect, gprNumber, rexR, rexB, modrmReg, modrmRm, UInt8.toBitVec]

def selectSecondBytes : List UInt8 := [0x48,0x8d,0xb4,0x24,0xc8,0x0,0x0,0x0,0x48,0x8d,0xbc,0x24,0x80,0x0,0x0,0x0,0x4c,0x89,0xf2,0x89,0xe9]

def selectSecondEffect (s : RamState) : Effect :=
  { rip := 0x110cbe
    writes := [⟨(.reg 6 : Operand 64), (Operand.reg 4 : Operand 64).read s + 200⟩,
      ⟨(.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s + 128⟩,
      ⟨(.reg 2 : Operand 64), (Operand.reg 14 : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), ((Operand.reg 5 : Operand 32).read s).setWidth 64⟩] }

theorem select_second_setup [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x110ca9)
      (codeRange 0x110ca9 selectSecondBytes) (Effect.post selectSecondEffect) := by
  advance_begin (lea_r64_effect_step 0x110ca9 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 200)) (by decide) rfl rfl)
  case next => intro _ _; exact boundary_ne_program hout (inProgram_of_textOffset 0x10cb1 (by decide))
  advance_then (lea_r64_effect_step 0x110cb1 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 128)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110ca9 selectSecondBytes 8 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x10cb9 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x110cb9 0x4c 0xf2 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x110ca9 selectSecondBytes 16 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x10cbc (by decide))⟩
  advance_then (mov_r32_r32_effect_step 0x110cbc 0xe9 rfl)
  case sub => exact codeRange_slice_subset 0x110ca9 selectSecondBytes 19 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x10cbe (by decide))⟩
  advance_finish [selectSecondEffect, gprNumber, rexR, rexB, modrmReg, modrmRm, UInt8.toBitVec]

theorem select_flag {s t : RamState} {value : BitVec 8}
    (flag : (s.regValue .rbp).setWidth 8 = value)
    (reg : t.regValue .rcx = ((s.regValue .rbp).setWidth 32).setWidth 64) :
    (t.regValue .rcx).setWidth 8 = value := by
  rw [reg, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),
    BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32)]
  exact flag

end P256.Proofs.Sec1.Affine.Uncompressed.Output
