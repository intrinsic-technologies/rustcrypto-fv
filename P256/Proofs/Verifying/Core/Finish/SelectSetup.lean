import P256.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Not.Generated.R.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Movs.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple
import P256.Proofs.Program.Code

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Verifying.Core.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def selectFirstBytes : List UInt8 :=
  [0x48,0x8d,0xbc,0x24,0x80,0x3,0x0,0x0,0x48,0x89,0xc6,0x89,0xd9]

def selectFirstEffect (s : RamState) : Effect :=
  { rip := 0x10dfd0
    writes := [⟨(.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s + 896⟩,
      ⟨(.reg 6 : Operand 64), (Operand.reg 0 : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), ((Operand.reg 3 : Operand 32).read s).setWidth 64⟩] }

theorem select_first_setup [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10dfc3)
      (codeRange 0x10dfc3 selectFirstBytes) (Effect.post selectFirstEffect) := by
  advance_begin (lea_r64_effect_step 0x10dfc3 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d32 896)) (by decide) rfl rfl)
  case next => intro _ _; exact boundary_ne_program hout (inProgram_of_textOffset 0xdfcb (by decide))
  advance_then (mov_r64_r64_effect_step 0x10dfcb 0x48 0xc6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10dfc3 selectFirstBytes 8 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xdfce (by decide))⟩
  advance_then (mov_r32_r32_effect_step 0x10dfce 0xd9 rfl)
  case sub => exact codeRange_slice_subset 0x10dfc3 selectFirstBytes 11 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xdfd0 (by decide))⟩
  advance_finish [selectFirstEffect, gprNumber, rexR, rexB, modrmReg, modrmRm, UInt8.toBitVec]

def selectSecondBytes : List UInt8 :=
  [0x48,0x8d,0xb4,0x24,0x60,0x2,0x0,0x0,0x48,0x8d,0x94,0x24,0xa0,0x0,0x0,0x0,0x48,0x8d,0xbc,0x24,0xa0,0x3,0x0,0x0,0x89,0xd9]

def selectSecondEffect (s : RamState) : Effect :=
  { rip := 0x10dfef
    writes := [⟨(.reg 6 : Operand 64), (Operand.reg 4 : Operand 64).read s + 608⟩,
      ⟨(.reg 2 : Operand 64), (Operand.reg 4 : Operand 64).read s + 160⟩,
      ⟨(.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s + 928⟩,
      ⟨(.reg 1 : Operand 64), ((Operand.reg 3 : Operand 32).read s).setWidth 64⟩] }

theorem select_second_setup [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10dfd5)
      (codeRange 0x10dfd5 selectSecondBytes) (Effect.post selectSecondEffect) := by
  advance_begin (lea_r64_effect_step 0x10dfd5 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d32 608)) (by decide) rfl rfl)
  case next => intro _ _; exact boundary_ne_program hout (inProgram_of_textOffset 0xdfdd (by decide))
  advance_then (lea_r64_effect_step 0x10dfdd 0x48 (by simp [RexWPrefix]) 2
    (.sib 4 none 0 (.d32 160)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dfd5 selectSecondBytes 8 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xdfe5 (by decide))⟩
  advance_then (lea_r64_effect_step 0x10dfe5 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d32 928)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dfd5 selectSecondBytes 16 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xdfed (by decide))⟩
  advance_then (mov_r32_r32_effect_step 0x10dfed 0xd9 rfl)
  case sub => exact codeRange_slice_subset 0x10dfd5 selectSecondBytes 24 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xdfef (by decide))⟩
  advance_finish [selectSecondEffect, gprNumber, rexR, rexB, modrmReg, modrmRm, UInt8.toBitVec]

theorem select_flag {s t : RamState} {value : BitVec 8}
    (flag : (s.regValue .rbx).setWidth 8 = value)
    (reg : t.regValue .rcx = ((s.regValue .rbx).setWidth 32).setWidth 64) :
    (t.regValue .rcx).setWidth 8 = value := by
  rw [reg, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),
    BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32)]
  exact flag

end P256.Proofs.Verifying.Core.Finish
