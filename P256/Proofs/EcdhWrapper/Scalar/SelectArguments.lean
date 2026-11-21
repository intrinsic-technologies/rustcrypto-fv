import P256.Proofs.Program.Code
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.Instructions.LegacyLoad
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Scalar

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program Prelude
open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions.LegacyLoad

attribute [local x86_compose] movR32M32LegacyEffect

structure SelectArgumentsPre (s : RamState) : Prop where
  rip : s.RIP = 0x1068b6
  readable : MemReadable s (stackPtr s + 408) 4

def selectArgumentBytes : List UInt8 :=
  [0x8b,0xac,0x24,0x98,0x01,0,0,0x4c,0x8d,0xb4,0x24,0xf0,0,0,0,
    0x48,0x8d,0x74,0x24,0x30,0x4c,0x89,0xf7,0x48,0x89,0xda,0x89,0xe9]

def selectArgumentEffect (s : RamState) : Effect :=
  { rip := 0x1068d2
    writes := [⟨(.reg 5 : Operand 64), ((.mem (stackPtr s+408) : Operand 32).read s).setWidth 64⟩,
      ⟨(.reg 14 : Operand 64), stackPtr s+240⟩,
      ⟨(.reg 6 : Operand 64), stackPtr s+48⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s+240⟩,
      ⟨(.reg 2 : Operand 64), (.reg 3 : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), ((.mem (stackPtr s+408) : Operand 32).read s).setWidth 64⟩] }

theorem select_arguments_loaded {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x1068b6 selectArgumentBytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0x68b6 _ (by decide) (by decide +kernel)

theorem select_arguments [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary SelectArgumentsPre (codeRange 0x1068b6 selectArgumentBytes)
      (Effect.post selectArgumentEffect) := by
  advance_begin (mov_r32_m32_legacy_effect_step 0x1068b6 5
    (.sib 4 none 0 (.d32 408)) (by decide +kernel) rfl rfl)
  case pre => intro s h; exact ⟨h.rip,h.readable⟩
  case next =>
    intro s h
    exact boundary_ne_program outside (inProgram_of_textOffset 0x68bd (by decide))
  advance_then (lea_r64_effect_step 0x1068bd 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 240)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1068b6 selectArgumentBytes 7 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x68c5 (by decide))
  advance_then (lea_r64_effect_step 0x1068c5 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 48)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1068b6 selectArgumentBytes 15 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x68ca (by decide))
  advance_then (mov_r64_r64_effect_step 0x1068ca 0x4c 0xf7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1068b6 selectArgumentBytes 20 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x68cd (by decide))
  advance_then (mov_r64_r64_effect_step 0x1068cd 0x48 0xda (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1068b6 selectArgumentBytes 23 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x68d0 (by decide))
  advance_then (mov_r32_r32_effect_step 0x1068d0 0xe9 rfl)
  case sub => exact codeRange_slice_subset 0x1068b6 selectArgumentBytes 26 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x68d2 (by decide))
  advance_finish [selectArgumentEffect,stackPtr,Operand.read_reg64,gprNumber,rexR,rexB,modrmReg,modrmRm,
    BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]

end P256.Proofs.EcdhWrapper.Scalar
