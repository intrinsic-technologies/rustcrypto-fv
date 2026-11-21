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

namespace P256.Proofs.Nonce.Update.Prepare.Key.Setup

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program

def bytes : List UInt8 := [0x49,0x89,0xd5,0x48,0x89,0xf5,0x48,0x89,0xfb]

def effect (s : RamState) : Effect :=
  { rip := 0x109f4a
    writes := [⟨(.reg 13 : Operand 64),(.reg 2 : Operand 64).read s⟩,
      ⟨(.reg 5 : Operand 64),(.reg 6 : Operand 64).read s⟩,
      ⟨(.reg 3 : Operand 64),(.reg 7 : Operand 64).read s⟩] }

theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x109f41 bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0x9f41 bytes (by decide) (by decide +kernel)

theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x109f41)
      (codeRange 0x109f41 bytes) (Effect.post effect) := by
  have h2 : gprNumber 0 (rexR (UInt8.toBitVec 73)) (modrmReg 213) = 2 := by decide +kernel
  have h6 : gprNumber 0 (rexR (UInt8.toBitVec 72)) (modrmReg 245) = 6 := by decide +kernel
  have h7 : gprNumber 0 (rexR (UInt8.toBitVec 72)) (modrmReg 251) = 7 := by decide +kernel
  advance_begin (mov_r64_r64_effect_step 0x109f41 0x49 0xd5 (by simp [RexWPrefix]) rfl)
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x9f44 (by decide))
  advance_then (mov_r64_r64_effect_step 0x109f44 0x48 0xf5 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x109f41 bytes 3 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x9f47 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x109f47 0x48 0xfb (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x109f41 bytes 6 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x9f4a (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hp hh
  apply hh.weaken
  · x86_norm [effect]
  · x86_norm [effect]
    exact ⟨congrArg (fun r => (Operand.reg r : Operand 64).read s) h2.symm,
      congrArg (fun r => (Operand.reg r : Operand 64).read s) h6.symm,
      congrArg (fun r => (Operand.reg r : Operand 64).read s) h7.symm⟩
  · intro i; cases i <;> x86_norm [effect]
  · x86_norm [effect]

end P256.Proofs.Nonce.Update.Prepare.Key.Setup
