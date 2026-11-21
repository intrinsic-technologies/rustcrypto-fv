import P256.Proofs.SecretKeyFromBytes.Scalar.Borrow
import P256.Proofs.Common.Instructions.ByteOps.Effects
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import P256.Proofs.Common.EffectCompose.Memory

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.SignatureFromDer.Fixed.Scalar.Decode

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def argumentBytes : List UInt8 :=
  [0x48,0x8d,0x7c,0x24,0x48,0x48,0x8d,0x54,0x24,0x28,0xbe,0x20,0x0,0x0,0x0,0xb9,0x4,0x0,0x0,0x0,0x41,0xb8,0x0,0x1,0x0,0x0]

def argumentEffect (s : RamState) : Effect :=
  { rip := 0x10faaa
    writes := [⟨(.reg 7 : Operand 64), stackPtr s + 72⟩,
      ⟨(.reg 2 : Operand 64), stackPtr s + 40⟩,
      ⟨(.reg 6 : Operand 64), 32⟩,
      ⟨(.reg 1 : Operand 64), 4⟩,
      ⟨(.reg 8 : Operand 64), 256⟩] }

theorem argument_correct [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10fa90) (codeRange 0x10fa90 argumentBytes)
      (Effect.post argumentEffect) := by
  advance_begin (lea_r64_effect_step 0x10fa90 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 72)) (by decide +kernel) rfl rfl)
  case next =>
    intro s h
    exact boundary_ne_program outside (inProgram_of_textOffset 0xfa95 (by decide))
  advance_then (lea_r64_effect_step 0x10fa95 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fa90 argumentBytes 5 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xfa9a (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10fa9a 0xbe (by decide +kernel) 32)
  case sub => exact codeRange_slice_subset 0x10fa90 argumentBytes 10 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xfa9f (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10fa9f 0xb9 (by decide +kernel) 4)
  case sub => exact codeRange_slice_subset 0x10fa90 argumentBytes 15 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xfaa4 (by decide))
  advance_then (mov_r32_imm32_rex_effect_step 0x10faa4 0x41 0xb8 (by simp [RexNoWPrefix]) (by decide +kernel) 256)
  case sub => exact codeRange_slice_subset 0x10fa90 argumentBytes 20 6
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xfaaa (by decide))
  advance_finish [argumentEffect, stackPtr, Operand.read_reg64]

end P256.Proofs.SignatureFromDer.Fixed.Scalar.Decode
