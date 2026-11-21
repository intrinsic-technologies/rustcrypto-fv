import P256.Proofs.Signing.Wrapper.Entry.Decode.Block

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Entry.Decode

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program Prelude
open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions

def EqualArgumentsPre (s : RamState) : Prop := s.RIP = 0x1025ba

def equalArgumentBytes : List UInt8 :=
  [72, 141, 188, 36, 24, 1, 0, 0, 72, 141, 148, 36, 176, 0, 0, 0, 190, 4, 0, 0, 0, 185, 4, 0, 0, 0]

def equalArgumentEffect (s : RamState) : Effect :=
  { rip := 0x1025d4
    writes := [⟨(.reg 7 : Operand 64), stackPtr s + 280⟩,
      ⟨(.reg 2 : Operand 64), stackPtr s + 176⟩,
      ⟨(.reg 6 : Operand 64), 0x4⟩,
      ⟨(.reg 1 : Operand 64), 0x4⟩] }

theorem equal_arguments [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary EqualArgumentsPre (codeRange 0x1025ba equalArgumentBytes)
      (Effect.post equalArgumentEffect) := by
  advance_begin (lea_r64_effect_step 0x1025ba 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 280)) (by decide +kernel) rfl rfl)
  case next =>
    intro s h
    exact boundary_ne_program outside (inProgram_of_textOffset 0x25c2 (by decide))
  advance_then (lea_r64_effect_step 0x1025c2 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 176)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1025ba equalArgumentBytes 8 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x25ca (by decide))
  advance_then (mov_r32_imm32_effect_step 0x1025ca 0xbe (by decide +kernel) 0x4)
  case sub => exact codeRange_slice_subset 0x1025ba equalArgumentBytes 16 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x25cf (by decide))
  advance_then (mov_r32_imm32_effect_step 0x1025cf 0xb9 (by decide +kernel) 0x4)
  case sub => exact codeRange_slice_subset 0x1025ba equalArgumentBytes 21 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x25d4 (by decide))
  advance_finish [equalArgumentEffect,stackPtr,Operand.read_reg64,State.regValue,BitVec.add_zero]
  all_goals (repeat constructor <;> rfl)

end P256.Proofs.Signing.Wrapper.Entry.Decode
