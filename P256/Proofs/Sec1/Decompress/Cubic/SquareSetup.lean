import P256.Proofs.Program.Code
import P256.Proofs.Common.Field.Montgomery.Schoolbook.Compose
import P256.Proofs.Common.Instructions.CrossPageStore
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

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Sec1.Decompress.Cubic

open P256.Spec.Program.Routines
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def squareBytes : List UInt8 :=
  [76, 141, 100, 36, 80, 72, 137, 230, 76, 137, 231, 76, 137, 250]

def squareEffect (s : RamState) : Effect :=
  { rip := 0x10fe0a
    writes := [⟨(Operand.reg 12 : Operand 64), (Operand.reg 4 : Operand 64).read s + 80⟩,
      ⟨(Operand.reg 6 : Operand 64), (Operand.reg 4 : Operand 64).read s⟩,
      ⟨(Operand.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s + 80⟩,
      ⟨(Operand.reg 2 : Operand 64), (Operand.reg 15 : Operand 64).read s⟩] }

theorem square_setup [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10fdfc) (codeRange 0x10fdfc squareBytes)
      (Effect.post squareEffect) := by
  advance_begin (lea_r64_effect_step 0x10fdfc 0x4c (by simp [RexWPrefix]) 12
    (.sib 4 none 0 (.d8 80)) (by decide +kernel) rfl rfl)
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0xfe01 (by decide))
  advance_then (mov_r64_r64_effect_step 0x10fe01 0x48 0xe6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10fdfc squareBytes 5 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfe04 (by decide))
  advance_then (mov_r64_r64_effect_step 0x10fe04 0x4c 0xe7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10fdfc squareBytes 8 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfe07 (by decide))
  advance_then (mov_r64_r64_effect_step 0x10fe07 0x4c 0xfa (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10fdfc squareBytes 11 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfe0a (by decide))
  advance_finish [squareEffect]

end P256.Proofs.Sec1.Decompress.Cubic
