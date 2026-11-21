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

namespace P256.Proofs.PublicPoint.Normalize.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def selectFirstBytes : List UInt8 := [0x48,0x89,0xdf,0x48,0x89,0xc6,0x89,0xe9]

def selectFirstEffect (s : RamState) : Effect :=
  { rip := 0x10eac1
    writes := [⟨(.reg 7 : Operand 64), (Operand.reg 3 : Operand 64).read s⟩,
      ⟨(.reg 6 : Operand 64), (Operand.reg 0 : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), ((Operand.reg 5 : Operand 32).read s).setWidth 64⟩] }

theorem select_first_setup [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10eab9)
      (codeRange 0x10eab9 selectFirstBytes) (Effect.post selectFirstEffect) := by
  advance_begin (mov_r64_r64_effect_step 0x10eab9 0x48 0xdf (by simp [RexWPrefix]) rfl)
  case next => intro _ _; exact boundary_ne_program hout (inProgram_of_textOffset 0xeabc (by decide))
  advance_then (mov_r64_r64_effect_step 0x10eabc 0x48 0xc6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10eab9 selectFirstBytes 3 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xeabf (by decide))⟩
  advance_then (mov_r32_r32_effect_step 0x10eabf 0xe9 rfl)
  case sub => exact codeRange_slice_subset 0x10eab9 selectFirstBytes 6 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xeac1 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t _ hH
  have hbx : gprNumber 0 (rexR (UInt8.toBitVec 0x48)) (modrmReg 0xdf) = 3 := by decide +kernel
  have hax : gprNumber 0 (rexR (UInt8.toBitVec 0x48)) (modrmReg 0xc6) = 0 := by decide +kernel
  have hbp : gprNumber 0 0 (modrmReg 0xe9) = 5 := by decide +kernel
  simp only [BitVec.ofNat_eq_ofNat] at hbx hax hbp
  apply hH.weaken
  · x86_norm [selectFirstEffect]
  · x86_norm [selectFirstEffect, hbx, hax, hbp]
    repeat constructor <;> rfl
  · intro i; cases i <;> x86_norm [selectFirstEffect]
  · x86_norm [selectFirstEffect]

def selectSecondBytes : List UInt8 :=
  [0x48,0x8d,0xb4,0x24,0x28,0x4,0x0,0x0,0x48,0x8d,0x94,0x24,0x28,0x1,0x0,0x0,0x48,0x8d,0x7b,0x20,0x89,0xe9]

def selectSecondEffect (s : RamState) : Effect :=
  { rip := 0x10eadc
    writes := [⟨(.reg 6 : Operand 64), (Operand.reg 4 : Operand 64).read s + 1064⟩,
      ⟨(.reg 2 : Operand 64), (Operand.reg 4 : Operand 64).read s + 296⟩,
      ⟨(.reg 7 : Operand 64), (Operand.reg 3 : Operand 64).read s + 32⟩,
      ⟨(.reg 1 : Operand 64), ((Operand.reg 5 : Operand 32).read s).setWidth 64⟩] }

theorem select_second_setup [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10eac6)
      (codeRange 0x10eac6 selectSecondBytes) (Effect.post selectSecondEffect) := by
  advance_begin (lea_r64_effect_step 0x10eac6 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d32 1064)) (by decide) rfl rfl)
  case next => intro _ _; exact boundary_ne_program hout (inProgram_of_textOffset 0xeace (by decide))
  advance_then (lea_r64_effect_step 0x10eace 0x48 (by simp [RexWPrefix]) 2
    (.sib 4 none 0 (.d32 296)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10eac6 selectSecondBytes 8 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xead6 (by decide))⟩
  advance_then (lea_r64_effect_step 0x10ead6 0x48 (by simp [RexWPrefix]) 7
    (.base 3 (.d8 32)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10eac6 selectSecondBytes 16 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xeada (by decide))⟩
  advance_then (mov_r32_r32_effect_step 0x10eada 0xe9 rfl)
  case sub => exact codeRange_slice_subset 0x10eac6 selectSecondBytes 20 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xeadc (by decide))⟩
  advance_finish [selectSecondEffect, gprNumber, rexR, rexB, modrmReg, modrmRm, UInt8.toBitVec]

theorem select_flag {s t : RamState} {value : BitVec 8}
    (flag : (s.regValue .rbp).setWidth 8 = value)
    (reg : t.regValue .rcx = ((s.regValue .rbp).setWidth 32).setWidth 64) :
    (t.regValue .rcx).setWidth 8 = value := by
  rw [reg, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),
    BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32)]
  exact flag

end P256.Proofs.PublicPoint.Normalize.Finish
