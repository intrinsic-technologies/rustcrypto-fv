import P256.Proofs.Signing.Wrapper.Entry.Decode.Block

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Entry.Decode

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program Prelude
open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions

def ArgumentsPre (s : RamState) : Prop := s.RIP = 0x102446

def decoderArgumentBytes : List UInt8 :=
  [72, 141, 188, 36, 80, 1, 0, 0, 72, 137, 226, 190, 32, 0, 0, 0, 185, 4, 0, 0, 0, 65, 184, 0, 1, 0, 0]

def decoderArgumentEffect (s : RamState) : Effect :=
  { rip := 0x102461
    writes := [⟨(.reg 7 : Operand 64), stackPtr s + 336⟩,
      ⟨(.reg 2 : Operand 64), (Operand.reg 4 : Operand 64).read s⟩,
      ⟨(.reg 6 : Operand 64), 0x20⟩,
      ⟨(.reg 1 : Operand 64), 0x4⟩,
      ⟨(.reg 8 : Operand 64), 0x100⟩] }

theorem decoder_arguments [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary ArgumentsPre (codeRange 0x102446 decoderArgumentBytes)
      (Effect.post decoderArgumentEffect) := by
  advance_begin (lea_r64_effect_step 0x102446 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 336)) (by decide +kernel) rfl rfl)
  case next =>
    intro s h
    exact boundary_ne_program outside (inProgram_of_textOffset 0x244e (by decide))
  advance_then (mov_r64_r64_effect_step 0x10244e 0x48 0xe2 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x102446 decoderArgumentBytes 8 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2451 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x102451 0xbe (by decide +kernel) 0x20)
  case sub => exact codeRange_slice_subset 0x102446 decoderArgumentBytes 11 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2456 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x102456 0xb9 (by decide +kernel) 0x4)
  case sub => exact codeRange_slice_subset 0x102446 decoderArgumentBytes 16 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x245b (by decide))
  advance_then (mov_r32_imm32_rex_effect_step 0x10245b 0x41 0xb8 (by simp [RexNoWPrefix]) (by decide +kernel) 0x100)
  case sub => exact codeRange_slice_subset 0x102446 decoderArgumentBytes 21 6
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2461 (by decide))
  advance_finish [decoderArgumentEffect,stackPtr,Operand.read_reg64,State.regValue,BitVec.add_zero]
  all_goals (repeat constructor <;> rfl)

end P256.Proofs.Signing.Wrapper.Entry.Decode
