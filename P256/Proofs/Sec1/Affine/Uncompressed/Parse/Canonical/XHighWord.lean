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

def xHighWordBytes : List UInt8 :=
  [73, 1, 196, 77, 1, 236, 72, 247, 208, 76, 9, 224, 72, 193, 232, 63]

def xHighWordEffect (s : RamState) : Effect :=
  { rip := 0x1108ca
    writes := [⟨(.reg 12 : Operand 64), ((Operand.reg 12 : Operand 64).read s)+((Operand.reg 0 : Operand 64).read s)+((Operand.reg 13 : Operand 64).read s)⟩,
      ⟨(.reg 0 : Operand 64), (~~~((Operand.reg 0 : Operand 64).read s) ||| (((Operand.reg 12 : Operand 64).read s)+((Operand.reg 0 : Operand 64).read s)+((Operand.reg 13 : Operand 64).read s))) >>> 63⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem x_high_word_correct [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1108ba)
      (codeRange 0x1108ba xHighWordBytes) (Effect.post xHighWordEffect) := by
  advance_begin (add_r64_r64_effect_step 0x1108ba 0x49 0xc4 (by simp [RexWPrefix]) rfl)
  case next =>
    intro _ _
    exact boundary_ne_program outside (inProgram_of_textOffset 0x108bd (by decide))
  advance_then (add_r64_r64_effect_step 0x1108bd 0x4d 0xec (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1108ba xHighWordBytes 3 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x108c0 (by decide))⟩
  advance_then (not_r64_effect_step 0x1108c0 0x48 0xd0 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1108ba xHighWordBytes 6 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x108c3 (by decide))⟩
  advance_then (or_r64_r64_effect_step 0x1108c3 0x4c 0xe0 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1108ba xHighWordBytes 9 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x108c6 (by decide))⟩
  advance_then (shr_r64_imm8_effect_step 0x1108c6 0x48 0xe8 63 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1108ba xHighWordBytes 12 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x108ca (by decide))⟩
  advance_finish [xHighWordEffect]

end P256.Proofs.Sec1.Affine.Uncompressed.Parse.Canonical
