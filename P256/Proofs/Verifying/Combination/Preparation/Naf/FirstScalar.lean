import P256.Proofs.Verifying.Combination.Entry

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Preparation.Naf.FirstScalar

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

def bytes : List UInt8 :=
  [0xba, 0x00, 0x01, 0x00, 0x00, 0x48, 0x8d, 0x5c, 0x24, 0x38, 0x48, 0x89, 0xdf]

def effect (s : RamState) : Effect :=
  { rip := 0x106646
    writes := [⟨(Operand.reg 2 : Operand 64), 256⟩,
      ⟨(Operand.reg 3 : Operand 64), stackPtr s + 56⟩,
      ⟨(Operand.reg 7 : Operand 64), stackPtr s + 56⟩] }

theorem run [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x106639)
      (codeRange 0x106639 bytes) (Effect.post effect) := by
  advance_begin (mov_r32_imm32_effect_step 0x106639 0xba (by decide) 256)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x663e (by decide))
  advance_then (lea_r64_effect_step 0x10663e 0x48 (by simp [RexWPrefix]) 3
    (.sib 4 none 0 (.d8 56)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x106639 bytes 5 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x6643 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x106643 0x48 0xdf (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x106639 bytes 10 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x6646 (by decide))⟩
  advance_finish [effect]

end P256.Proofs.Verifying.Combination.Preparation.Naf.FirstScalar
