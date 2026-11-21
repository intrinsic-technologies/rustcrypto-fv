import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.Field.Operations.Neg.Borrow.Or
import P256.Proofs.Program.Code
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
open P256.Proofs.Common.Field.FieldNeg.Instructions (or_r64_r64_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice)

namespace P256.Proofs.Sec1.Decompress.Input

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def canonicalLowWordBytes : List UInt8 :=
  [0x48,0x8d,0x72,0x01,0x48,0xf7,0xd2,0x48,0x09,0xf2,0x48,0xc1,0xea,0x3f]

def canonicalLowWordEffect (s : RamState) : Effect :=
  let x := (Operand.reg 2 : Operand 64).read s
  { rip := 0x10fc52
    writes := [⟨(Operand.reg 6 : Operand 64), x + 1⟩,
      ⟨(Operand.reg 2 : Operand 64), (~~~x ||| (x + 1)) >>> 63⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem canonical_low_word_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10fc44)
      (codeRange 0x10fc44 canonicalLowWordBytes) (Effect.post canonicalLowWordEffect) := by
  advance_begin (lea_r64_effect_step 0x10fc44 0x48 (by unfold RexWPrefix; decide +kernel)
    6 (.base 2 (.d8 1)) (by decide +kernel) rfl rfl)
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0xfc48 (by decide +kernel))
  advance_then (not_r64_effect_step 0x10fc48 0x48 0xd2
    (by unfold RexWPrefix; decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fc44 canonicalLowWordBytes 4 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfc4b (by decide +kernel))
  advance_then (or_r64_r64_effect_step 0x10fc4b 0x48 0xf2
    (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x10fc44 canonicalLowWordBytes 7 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfc4e (by decide +kernel))
  advance_then (shr_r64_imm8_effect_step 0x10fc4e 0x48 0xea 63
    (by unfold RexWPrefix; decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fc44 canonicalLowWordBytes 10 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfc52 (by decide +kernel))
  advance_finish [canonicalLowWordEffect]

end P256.Proofs.Sec1.Decompress.Input
