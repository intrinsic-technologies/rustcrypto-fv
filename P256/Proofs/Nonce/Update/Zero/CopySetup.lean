import P256.Proofs.Common.Field.Operations.Run.Compose
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

namespace P256.Proofs.Nonce.Update.Zero.CopySetup

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program

def bytes : List UInt8 :=
  [0x48, 0x8d, 0x9c, 0x24, 0xb0, 0x1, 0x0, 0x0, 0x48, 0x8d, 0x74, 0x24, 0x58, 0xba, 0xa8, 0x0, 0x0, 0x0, 0x48, 0x89, 0xdf]

def effect (s : RamState) : Effect :=
  { rip := 0x10a3b1
    writes := [⟨(.reg 3 : Operand 64), rspOf s + 432⟩,
      ⟨(.reg 6 : Operand 64), rspOf s + 88⟩,
      ⟨(.reg 2 : Operand 64), 168⟩,
      ⟨(.reg 7 : Operand 64), rspOf s + 432⟩] }

theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10a39c)
      (codeRange 0x10a39c bytes) (Effect.post effect) := by
  advance_begin (lea_r64_effect_step 0x10a39c 0x48 (by simp [RexWPrefix]) 3
    (.sib 4 none 0 (.d32 432)) (by decide +kernel) rfl rfl)
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xa3a4 (by decide))
  advance_then (lea_r64_effect_step 0x10a3a4 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d8 88)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a39c bytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa3a9 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10a3a9 0xba (by decide) 168)
  case sub => exact codeRange_slice_subset 0x10a39c bytes 13 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa3ae (by decide))
  advance_then (mov_r64_r64_effect_step 0x10a3ae 0x48 0xdf (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10a39c bytes 18 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa3b1 (by decide))
  advance_finish [effect]

end P256.Proofs.Nonce.Update.Zero.CopySetup
