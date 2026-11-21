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

def xSecondWordBytes : List UInt8 :=
  [73, 1, 247, 73, 1, 255, 72, 247, 214, 76, 33, 254, 72, 193, 238, 63]

def xSecondWordEffect (s : RamState) : Effect :=
  { rip := 0x11088f
    writes := [⟨(.reg 15 : Operand 64), ((Operand.reg 15 : Operand 64).read s)+((Operand.reg 6 : Operand 64).read s)+((Operand.reg 7 : Operand 64).read s)⟩,
      ⟨(.reg 6 : Operand 64), (~~~((Operand.reg 6 : Operand 64).read s) &&& (((Operand.reg 15 : Operand 64).read s)+((Operand.reg 6 : Operand 64).read s)+((Operand.reg 7 : Operand 64).read s))) >>> 63⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem x_second_word_correct [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x11087f)
      (codeRange 0x11087f xSecondWordBytes) (Effect.post xSecondWordEffect) := by
  advance_begin (add_r64_r64_effect_step 0x11087f 0x49 0xf7 (by simp [RexWPrefix]) rfl)
  case next =>
    intro _ _
    exact boundary_ne_program outside (inProgram_of_textOffset 0x10882 (by decide))
  advance_then (add_r64_r64_effect_step 0x110882 0x49 0xff (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x11087f xSecondWordBytes 3 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x10885 (by decide))⟩
  advance_then (not_r64_effect_step 0x110885 0x48 0xd6 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11087f xSecondWordBytes 6 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x10888 (by decide))⟩
  advance_then (and_r64_r64_effect_step 0x110888 0x4c 0xfe (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x11087f xSecondWordBytes 9 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x1088b (by decide))⟩
  advance_then (shr_r64_imm8_effect_step 0x11088b 0x48 0xee 63 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11087f xSecondWordBytes 12 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x1088f (by decide))⟩
  advance_finish [xSecondWordEffect]

end P256.Proofs.Sec1.Affine.Uncompressed.Parse.Canonical
