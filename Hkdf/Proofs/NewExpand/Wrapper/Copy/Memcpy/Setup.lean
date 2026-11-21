import Hkdf.Proofs.Common.Field.Operations.Run.Compose
import Hkdf.Proofs.Common.Machine.Code
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Wrapper.Copy.Memcpy

open Hkdf.Spec.Program Hkdf.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Field Hkdf.Proofs.Common.Machine

def setupBytes : List UInt8 :=
  [0x48, 0x8d, 0x74, 0x24, 0x20, 0x4c, 0x8d, 0xac, 0x24, 0xb0, 0, 0, 0,
   0xba, 0x90, 0, 0, 0, 0x4c, 0x89, 0xef]

def setupEffect (s : RamState) : Effect :=
  { rip := 0x10201f
    writes := [⟨(.reg 6 : Operand 64), rspOf s + 32⟩,
      ⟨(.reg 13 : Operand 64), rspOf s + 176⟩,
      ⟨(.reg 2 : Operand 64), 144⟩,
      ⟨(.reg 7 : Operand 64), rspOf s + 176⟩] }

theorem setup_code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x10200a setupBytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0x200a setupBytes
    (by decide +kernel) (by decide +kernel)

theorem setup_run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s ↦ s.RIP = 0x10200a)
      (codeRange 0x10200a setupBytes) (Effect.post setupEffect) := by
  advance_begin (lea_r64_effect_step 0x10200a 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl)
  case next => exact fun _ _ ↦ boundary_ne_program outside (inProgram_of_textOffset 0x200f (by decide))
  advance_then (lea_r64_effect_step 0x10200f 0x4c (by simp [RexWPrefix]) 5
    (.sib 4 none 0 (.d32 176)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10200a setupBytes 5 8
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0x2017 (by decide))⟩
  advance_then (mov_r32_imm32_effect_step 0x102017 0xba (by decide) 144)
  case sub => exact codeRange_slice_subset 0x10200a setupBytes 13 5
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0x201c (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10201c 0x4c 0xef (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10200a setupBytes 18 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0x201f (by decide))⟩
  advance_finish [setupEffect]

end Hkdf.Proofs.NewExpand.Wrapper.Copy.Memcpy
