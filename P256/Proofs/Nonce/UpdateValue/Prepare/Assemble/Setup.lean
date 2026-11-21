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

namespace P256.Proofs.Nonce.UpdateValue.Prepare.Assemble.Setup

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program

def bytes : List UInt8 :=
  [0x48, 0x8d, 0xbc, 0x24, 0x50, 0x1, 0x0, 0x0, 0x48, 0x8d, 0x74, 0x24, 0x68, 0xb9, 0xd, 0x0, 0x0, 0x0]

def effect (s : RamState) : Effect :=
  { rip := 0x10aa70
    writes := [⟨(.reg 7 : Operand 64), rspOf s + 336⟩,
      ⟨(.reg 6 : Operand 64), rspOf s + 104⟩,
      ⟨(.reg 1 : Operand 64), 13⟩] }

theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x10aa5e bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xaa5e bytes
    (by decide +kernel) (by decide +kernel)

theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10aa5e)
      (codeRange 0x10aa5e bytes) (Effect.post effect) := by
  advance_begin (lea_r64_effect_step 0x10aa5e 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d32 336)) (by decide +kernel) rfl rfl)
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xaa66 (by decide))
  advance_then (lea_r64_effect_step 0x10aa66 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d8 104)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10aa5e bytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xaa6b (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10aa6b 0xb9 (by decide) 13)
  case sub => exact codeRange_slice_subset 0x10aa5e bytes 13 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xaa70 (by decide))
  advance_finish [effect]

end P256.Proofs.Nonce.UpdateValue.Prepare.Assemble.Setup
