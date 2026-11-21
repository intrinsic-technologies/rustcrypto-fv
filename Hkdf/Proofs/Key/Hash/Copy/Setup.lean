import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.EffectCompose.Advance
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.Key.Hash.Copy.Setup

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.Field (AdvanceTriple)

def bytes : List UInt8 :=
  [0x48, 0x8d, 0x7c, 0x24, 0x40, 0xb9, 0x0d, 0, 0, 0, 0x4c, 0x89, 0xe6]

def effect (s : RamState) : Effect :=
  { rip := 0x11643f
    writes := [⟨(.reg 7 : Operand 64), rspOf s + 64⟩,
      ⟨(.reg 1 : Operand 64), 13⟩,
      ⟨(.reg 6 : Operand 64), s.regValue .r12⟩] }

theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x116432 bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0x16432 bytes
    (by decide +kernel) (by decide +kernel)

theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x116432)
      (codeRange 0x116432 bytes) (Effect.post effect) := by
  advance_begin (show StepEffect _ _ (leaR64Effect 0x116432 7 (.sib 4 none 0 (.d8 64))) from
    lea_r64_effect_step 0x116432 0x48 (by simp [RexWPrefix]) 7
      (.sib 4 none 0 (.d8 64)) (by decide) rfl rfl)
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0x16437 (by decide))
  advance_then (show StepEffect _ _ (movR32Imm32Effect 0x116437 5 1 13) from
    mov_r32_imm32_effect_step 0x116437 0xb9 (by decide) 13)
  case sub => exact codeRange_slice_subset 0x116432 bytes 5 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1643c (by decide))
  advance_then (show StepEffect _ _ (movR64R64Effect 0x11643c 6 12) from
    mov_r64_r64_effect_step 0x11643c 0x4c 0xe6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x116432 bytes 10 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1643f (by decide))
  advance_finish [effect]

end Hkdf.Proofs.Key.Hash.Copy.Setup
