import P256.Proofs.Program.Code
import P256.Proofs.Common.Field.Operations.Run.Compose
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

open P256.Proofs.Common.Instructions.MovzxByte (movzx_r32_r8_effect_step)
open P256.Proofs.Program
open P256.Proofs.Common.Field (AdvanceTriple)

namespace P256.Proofs.Sec1.SquareRoot

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def selectSetupBytes : List UInt8 :=
  [0x0f,0xb6,0xe8,0x48,0x8d,0x7c,0x24,0x30,0x48,0x8d,0x54,0x24,8,
    0xbe,4,0,0,0,0xb9,4,0,0,0,0x41,0x89,0xe8]

def selectSetupEffect (s : RamState) : Effect :=
  { rip := 0x114594
    writes := [⟨(Operand.reg 5 : Operand 64), ((Operand.reg 0 : Operand 64).read s).setWidth 8 |>.setWidth 64⟩,
      ⟨(Operand.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s+48⟩,
      ⟨(Operand.reg 2 : Operand 64), (Operand.reg 4 : Operand 64).read s+8⟩,
      ⟨(Operand.reg 6 : Operand 64),4⟩,⟨(Operand.reg 1 : Operand 64),4⟩,
      ⟨(Operand.reg 8 : Operand 64), ((Operand.reg 0 : Operand 64).read s).setWidth 8 |>.setWidth 64⟩] }

theorem select_setup_code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x11457a selectSetupBytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0x1457a selectSetupBytes
    (by decide +kernel) (by decide +kernel)

theorem select_setup [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP=0x11457a) (codeRange 0x11457a selectSetupBytes)
      (Effect.post selectSetupEffect) := by
  have er : gprNumber 0#1 0#1 (modrmRm 0xe8) = 0#5 := by decide +kernel
  have hw (x : BitVec 8) : ((x.setWidth 64).setWidth 32).setWidth 64 = x.setWidth 64 := by
    rw [BitVec.setWidth_setWidth_of_le x (show 32 ≤ 64 by decide), BitVec.setWidth_setWidth (by decide)]
  advance_begin (movzx_r32_r8_effect_step 0x11457a 0xe8 rfl (by decide +kernel))
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0x1457d (by decide))
  advance_then (lea_r64_effect_step 0x11457d 0x48 (by simp [RexWPrefix])
    7 (.sib 4 none 0 (.d8 48)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11457a selectSetupBytes 3 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem; simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x14582 (by decide))
  advance_then (lea_r64_effect_step 0x114582 0x48 (by simp [RexWPrefix])
    2 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11457a selectSetupBytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem; simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x14587 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x114587 0xbe (by decide +kernel) 4)
  case sub => exact codeRange_slice_subset 0x11457a selectSetupBytes 13 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem; simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1458c (by decide))
  advance_then (mov_r32_imm32_effect_step 0x11458c 0xb9 (by decide +kernel) 4)
  case sub => exact codeRange_slice_subset 0x11457a selectSetupBytes 18 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem; simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x14591 (by decide))
  advance_then (mov_r32_r32_rex_effect_step 0x114591 0x41 0xe8 (by simp [RexNoWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x11457a selectSetupBytes 23 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem; simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x14594 (by decide))
  advance_finish [selectSetupEffect, er, hw]

end P256.Proofs.Sec1.SquareRoot
