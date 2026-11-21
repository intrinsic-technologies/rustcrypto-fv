import P256.Proofs.Program.Code
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.EffectCompose
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
import X86Proofs.Instructions.NopMem.Triple
import X86Proofs.Program.Entry

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice readyToStep)

namespace P256.Proofs.Projective.Multiply.Machine.Radix

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def extractionFinishBytes : List UInt8 :=
  [0xb9,2,0,0,0,0x66,0x0f,0x1f,0x84,0,0,0,0,0]

def extractionFinishEffect (_ : RamState) : Effect :=
  {rip := 0x10ba30, writes := [⟨(Operand.reg 1 : Operand 64),2⟩], flags := none}

theorem extraction_finish_block [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10ba22) (codeRange 0x10ba22 extractionFinishBytes)
      (Effect.post extractionFinishEffect) := by
  advance_begin (mov_r32_imm32_effect_step 0x10ba22 0xb9 (by decide) 2)
  case next => exact fun s h => boundary_ne_program outside (inProgram_of_textOffset 0xba27 (by decide))
  advance_then (nop_m_effect_step 0x10ba27 [0x66] (by decide) (by decide)
    (.sib 0 (some 0) 0 (.d32 0)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10ba22 extractionFinishBytes 5 9
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip,?_,?_⟩
    · exact nopEffect_avoids _ _ _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xba30 (by decide))
  advance_finish [extractionFinishEffect,nopEffect]


end P256.Proofs.Projective.Multiply.Machine.Radix
