import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Program.Code
import P256.Proofs.Common.Instructions.MovzxByte
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

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions.MovzxByte (movzx_r32_r8_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Sec1.Decompress.Input

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def prepareBytes : List UInt8 :=
  [0xf, 0xb6, 0xe8, 0x48, 0x8d, 0x7c, 0x24, 0x50, 0xbe, 0x4, 0x0, 0x0, 0x0, 0xb9, 0x4, 0x0, 0x0, 0x0, 0x4c, 0x89, 0xfa, 0x41, 0x89, 0xe8]

def prepareEffect (s : RamState) : Effect :=
  { rip := 0x10fd3c
    writes := [⟨(Operand.reg 5 : Operand 64), ((Operand.reg 0 : Operand 64).read s).setWidth 8 |>.setWidth 64⟩,
      ⟨(Operand.reg 7 : Operand 64), stackPtr s+80⟩,
      ⟨(Operand.reg 6 : Operand 64), 4⟩, ⟨(Operand.reg 1 : Operand 64), 4⟩,
      ⟨(Operand.reg 2 : Operand 64), (Operand.reg 15 : Operand 64).read s⟩,
      ⟨(Operand.reg 8 : Operand 64), ((Operand.reg 0 : Operand 64).read s).setWidth 8 |>.setWidth 64⟩] }

theorem prepare_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP=0x10fd24) (codeRange 0x10fd24 prepareBytes)
      (Effect.post prepareEffect) := by
  have er0 : gprNumber 0 0 (modrmRm 0xe8) = 0#5 := by decide +kernel
  have er15 : gprNumber 0 (rexR (UInt8.toBitVec 0x4c)) (modrmReg 0xfa) = 15#5 := by decide +kernel
  have hw (x : BitVec 8) : ((x.setWidth 64).setWidth 32).setWidth 64 = x.setWidth 64 := by
    rw [BitVec.setWidth_setWidth_of_le x (show 32 ≤ 64 by decide), BitVec.setWidth_setWidth (by decide)]
  simp only [BitVec.ofNat_eq_ofNat] at er0 er15
  advance_begin (movzx_r32_r8_effect_step 0x10fd24 0xe8 rfl (by decide +kernel))
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0xfd27 (by decide))
  advance_then (lea_r64_effect_step 0x10fd27 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 80)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fd24 prepareBytes 3 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem; simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfd2c (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10fd2c 0xbe (by decide +kernel) 4)
  case sub => exact codeRange_slice_subset 0x10fd24 prepareBytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem; simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfd31 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10fd31 0xb9 (by decide +kernel) 4)
  case sub => exact codeRange_slice_subset 0x10fd24 prepareBytes 13 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem; simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfd36 (by decide))
  advance_then (mov_r64_r64_effect_step 0x10fd36 0x4c 0xfa (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10fd24 prepareBytes 18 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem; simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfd39 (by decide))
  advance_then (mov_r32_r32_rex_effect_step 0x10fd39 0x41 0xe8 (by simp [RexNoWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10fd24 prepareBytes 21 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem; simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfd3c (by decide))
  advance_finish [prepareEffect, stackPtr, Operand.read_reg64, hw, er0, er15]

end P256.Proofs.Sec1.Decompress.Input
