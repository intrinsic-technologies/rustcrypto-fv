import P256.Proofs.Program.Code
import P256.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Scalar

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program Prelude
open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

def argumentBytes : List UInt8 :=
  [0x48,0x8d,0x9c,0x24,0x78,0x01,0x00,0x00,0x48,0x8d,0x74,0x24,0x70,0x48,0x89,0xdf]

def argumentEffect (s : RamState) : Effect :=
  { rip := 0x10688d
    writes := [⟨(.reg 3 : Operand 64), stackPtr s + 376⟩,
      ⟨(.reg 6 : Operand 64), stackPtr s + 112⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 376⟩] }

theorem arguments [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10687d)
      (codeRange 0x10687d argumentBytes) (Effect.post argumentEffect) := by
  advance_begin (lea_r64_effect_step 0x10687d 0x48 (by simp [RexWPrefix]) 3
    (.sib 4 none 0 (.d32 376)) (by decide +kernel) rfl rfl)
  case next =>
    intro s h
    exact boundary_ne_program outside (inProgram_of_textOffset 0x6885 (by decide))
  advance_then (lea_r64_effect_step 0x106885 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d8 112)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10687d argumentBytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x688a (by decide))
  advance_then (mov_r64_r64_effect_step 0x10688a 0x48 0xdf (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10687d argumentBytes 13 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x688d (by decide))
  advance_finish [argumentEffect, stackPtr, Operand.read_reg64]

end P256.Proofs.EcdhWrapper.Scalar
