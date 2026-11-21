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

def yThirdWordBytes : List UInt8 :=
  [72, 1, 207, 72, 247, 209, 72, 33, 249, 72, 193, 233, 63]

def yThirdWordEffect (s : RamState) : Effect :=
  { rip := 0x1106cc
    writes := [⟨(.reg 7 : Operand 64), ((Operand.reg 7 : Operand 64).read s)+((Operand.reg 1 : Operand 64).read s)⟩,
      ⟨(.reg 1 : Operand 64), (~~~((Operand.reg 1 : Operand 64).read s) &&& (((Operand.reg 7 : Operand 64).read s)+((Operand.reg 1 : Operand 64).read s))) >>> 63⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem y_third_word_correct [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1106bf)
      (codeRange 0x1106bf yThirdWordBytes) (Effect.post yThirdWordEffect) := by
  advance_begin (add_r64_r64_effect_step 0x1106bf 0x48 0xcf (by simp [RexWPrefix]) rfl)
  case next =>
    intro _ _
    exact boundary_ne_program outside (inProgram_of_textOffset 0x106c2 (by decide))
  advance_then (not_r64_effect_step 0x1106c2 0x48 0xd1 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1106bf yThirdWordBytes 3 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x106c5 (by decide))⟩
  advance_then (and_r64_r64_effect_step 0x1106c5 0x48 0xf9 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1106bf yThirdWordBytes 6 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x106c8 (by decide))⟩
  advance_then (shr_r64_imm8_effect_step 0x1106c8 0x48 0xe9 63 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1106bf yThirdWordBytes 9 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x106cc (by decide))⟩
  advance_finish [yThirdWordEffect]

end P256.Proofs.Sec1.Affine.Uncompressed.Parse.Canonical
