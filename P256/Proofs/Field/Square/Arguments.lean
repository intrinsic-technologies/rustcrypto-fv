import P256.Proofs.Field.Montgomery.Prologue

set_option autoImplicit false

namespace P256.Proofs.Field.Square

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

def argumentBytes : List UInt8 :=
  [0x48,0x89,0xfb,0x48,0x8d,0x7c,0x24,0x40,0xba,4,0,0,0,
   0x41,0xb8,4,0,0,0,0x48,0x89,0xf1]

def argumentEffect (s : RamState) : Effect :=
  { rip := 0x11381e
    writes := [⟨(.reg 1 : Operand 64), s.regValue .rsi⟩,
      ⟨(.reg 3 : Operand 64), s.regValue .rdi⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 64⟩,
      ⟨(.reg 2 : Operand 64), 4⟩, ⟨(.reg 8 : Operand 64), 4⟩] }

theorem arguments [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x113808) (codeRange 0x113808 argumentBytes)
      (Effect.post argumentEffect) := by
  advance_begin (mov_r64_r64_effect_step 0x113808 0x48 0xfb
    (by simp [RexWPrefix]) rfl)
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0x1380b (by decide))
  advance_then (lea_r64_effect_step 0x11380b 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d8 64)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113808 argumentBytes 3 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13810 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x113810 0xba (by decide +kernel) 4)
  case sub => exact codeRange_slice_subset 0x113808 argumentBytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13815 (by decide))
  advance_then (mov_r32_imm32_rex_effect_step 0x113815 0x41 0xb8
    (by simp [RexNoWPrefix]) (by decide +kernel) 4)
  case sub => exact codeRange_slice_subset 0x113808 argumentBytes 13 6
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1381b (by decide))
  advance_then (mov_r64_r64_effect_step 0x11381b 0x48 0xf1
    (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x113808 argumentBytes 19 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1381e (by decide))
  advance_finish [argumentEffect, stackPtr, Operand.read_reg64]

end P256.Proofs.Field.Square
