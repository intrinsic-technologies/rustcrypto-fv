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

namespace P256.Proofs.Sec1.Affine.Uncompressed.Parse.Canonical

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def yLowWordBytes : List UInt8 :=
  [76, 141, 66, 1, 72, 247, 210, 76, 9, 194, 72, 193, 234, 63]

def yLowWordEffect (s : RamState) : Effect :=
  let x := (Operand.reg 2 : Operand 64).read s
  { rip := 0x11067f
    writes := [⟨(Operand.reg 8 : Operand 64), x + 1⟩,
      ⟨(Operand.reg 2 : Operand 64), (~~~x ||| (x + 1)) >>> 63⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem y_low_word_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x110671)
      (codeRange 0x110671 yLowWordBytes) (Effect.post yLowWordEffect) := by
  advance_begin (lea_r64_effect_step 0x110671 0x4c (by unfold RexWPrefix; decide +kernel)
    0 (.base 2 (.d8 1)) (by decide +kernel) rfl rfl)
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0x10675 (by decide +kernel))
  advance_then (not_r64_effect_step 0x110675 0x48 0xd2
    (by unfold RexWPrefix; decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110671 yLowWordBytes 4 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x10678 (by decide +kernel))
  advance_then (or_r64_r64_effect_step 0x110678 0x4c 0xc2
    (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x110671 yLowWordBytes 7 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1067b (by decide +kernel))
  advance_then (shr_r64_imm8_effect_step 0x11067b 0x48 0xea 63
    (by unfold RexWPrefix; decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110671 yLowWordBytes 10 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1067f (by decide +kernel))
  advance_finish [yLowWordEffect]

end P256.Proofs.Sec1.Affine.Uncompressed.Parse.Canonical
