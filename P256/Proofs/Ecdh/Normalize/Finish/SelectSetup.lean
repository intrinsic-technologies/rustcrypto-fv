import P256.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple
import P256.Proofs.Program.Code

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Ecdh.Normalize.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def selectFirstBytes : List UInt8 := [0x48,0x8d,0x7c,0x24,0x50,0x48,0x89,0xc6,0x89,0xe9]

def selectFirstEffect (s : RamState) : Effect :=
  { rip := 0x1004c5
    writes := [⟨(.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s + 80⟩,
      ⟨(.reg 6 : Operand 64), (Operand.reg 0 : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), ((Operand.reg 5 : Operand 32).read s).setWidth 64⟩] }

theorem select_first_setup [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1004bb)
      (codeRange 0x1004bb selectFirstBytes) (Effect.post selectFirstEffect) := by
  advance_begin (lea_r64_effect_step 0x1004bb 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d8 80)) (by decide) rfl rfl)
  case next => intro _ _; exact boundary_ne_program hout (inProgram_of_textOffset 0x4c0 (by decide))
  advance_then (mov_r64_r64_effect_step 0x1004c0 0x48 0xc6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1004bb selectFirstBytes 5 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x4c3 (by decide))⟩
  advance_then (mov_r32_r32_effect_step 0x1004c3 0xe9 rfl)
  case sub => exact codeRange_slice_subset 0x1004bb selectFirstBytes 8 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x4c5 (by decide))⟩
  advance_finish [selectFirstEffect, gprNumber, rexR, rexB, modrmReg, modrmRm, UInt8.toBitVec]

def selectSecondBytes : List UInt8 :=
  [0x48,0x8d,0xb4,0x24,0x18,0x1,0x0,0x0,0x48,0x8d,0x94,0x24,0x18,0x4,0x0,0x0,0x48,0x8d,0x7c,0x24,0x70,0x89,0xe9]

def selectSecondEffect (s : RamState) : Effect :=
  { rip := 0x1004e1
    writes := [⟨(.reg 6 : Operand 64), (Operand.reg 4 : Operand 64).read s + 280⟩,
      ⟨(.reg 2 : Operand 64), (Operand.reg 4 : Operand 64).read s + 1048⟩,
      ⟨(.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s + 112⟩,
      ⟨(.reg 1 : Operand 64), ((Operand.reg 5 : Operand 32).read s).setWidth 64⟩] }

theorem select_second_setup [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1004ca)
      (codeRange 0x1004ca selectSecondBytes) (Effect.post selectSecondEffect) := by
  advance_begin (lea_r64_effect_step 0x1004ca 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d32 280)) (by decide) rfl rfl)
  case next => intro _ _; exact boundary_ne_program hout (inProgram_of_textOffset 0x4d2 (by decide))
  advance_then (lea_r64_effect_step 0x1004d2 0x48 (by simp [RexWPrefix]) 2
    (.sib 4 none 0 (.d32 1048)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1004ca selectSecondBytes 8 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x4da (by decide))⟩
  advance_then (lea_r64_effect_step 0x1004da 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d8 112)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1004ca selectSecondBytes 16 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x4df (by decide))⟩
  advance_then (mov_r32_r32_effect_step 0x1004df 0xe9 rfl)
  case sub => exact codeRange_slice_subset 0x1004ca selectSecondBytes 21 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x4e1 (by decide))⟩
  advance_finish [selectSecondEffect, gprNumber, rexR, rexB, modrmReg, modrmRm, UInt8.toBitVec]

theorem select_flag {s t : RamState} {value : BitVec 8}
    (flag : (s.regValue .rbp).setWidth 8 = value)
    (reg : t.regValue .rcx = ((s.regValue .rbp).setWidth 32).setWidth 64) :
    (t.regValue .rcx).setWidth 8 = value := by
  rw [reg, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),
    BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32)]
  exact flag

end P256.Proofs.Ecdh.Normalize.Finish
