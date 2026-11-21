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

namespace P256.Proofs.Nonce.Update.Prepare.Assemble.Setup

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program

def bytes : List UInt8 :=
  [0x48, 0x8d, 0xbc, 0x24, 0xf0, 0x1, 0x0, 0x0, 0x48, 0x8d, 0xb4, 0x24, 0x0, 0x1, 0x0, 0x0, 0xb9, 0xd, 0x0, 0x0, 0x0]

def effect (s : RamState) : Effect :=
  { rip := 0x10a0a3
    writes := [⟨(.reg 7 : Operand 64), rspOf s + 496⟩,
      ⟨(.reg 6 : Operand 64), rspOf s + 256⟩,
      ⟨(.reg 1 : Operand 64), 13⟩] }

theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x10a08e bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xa08e bytes
    (by decide +kernel) (by decide +kernel)

theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10a08e)
      (codeRange 0x10a08e bytes) (Effect.post effect) := by
  advance_begin (lea_r64_effect_step 0x10a08e 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d32 496)) (by decide +kernel) rfl rfl)
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xa096 (by decide))
  advance_then (lea_r64_effect_step 0x10a096 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d32 256)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a08e bytes 8 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa09e (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10a09e 0xb9 (by decide) 13)
  case sub => exact codeRange_slice_subset 0x10a08e bytes 16 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa0a3 (by decide))
  advance_finish [effect]

end P256.Proofs.Nonce.Update.Prepare.Assemble.Setup
