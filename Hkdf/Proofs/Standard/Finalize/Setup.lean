import Hkdf.Proofs.Standard.Memory
import Hkdf.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Finalize

open Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.Field

def copySetupBytes : List UInt8 :=
  [0x48,0x8d,0x9c,0x24,0x48,1,0,0,0x48,0x8d,0x74,0x24,0x78,
    0xba,0x90,0,0,0,0x48,0x89,0xdf]

def copySetupEffect (s : RamState) : Effect :=
  { rip := 0x101739
    writes := [
      ⟨(.reg 3 : Operand 64), rspOf s + 328⟩,
      ⟨(.reg 6 : Operand 64), rspOf s + 120⟩,
      ⟨(.reg 2 : Operand 64), 144⟩,
      ⟨(.reg 7 : Operand 64), rspOf s + 328⟩] }

theorem copySetup_code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x101724 copySetupBytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0x1724 copySetupBytes
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 800000 in
theorem copySetup_run [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s ↦ s.RIP = 0x101724)
      (codeRange 0x101724 copySetupBytes) (Effect.post copySetupEffect) := by
  advance_begin (lea_r64_effect_step 0x101724 0x48 (by simp [RexWPrefix]) 3
    (.sib 4 none 0 (.d32 328)) (by decide +kernel) rfl rfl)
  case next => exact fun _ _ ↦ boundary_ne_program outside (inProgram_of_textOffset 0x172c (by decide))
  advance_then (lea_r64_effect_step 0x10172c 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d8 120)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x101724 copySetupBytes 8 5
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0x1731 (by decide))⟩
  advance_then (mov_r32_imm32_effect_step 0x101731 0xba (by decide) 144)
  case sub => exact codeRange_slice_subset 0x101724 copySetupBytes 13 5
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0x1736 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x101736 0x48 0xdf (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x101724 copySetupBytes 18 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0x1739 (by decide))⟩
  advance_finish [copySetupEffect]

def finalizerSetupBytes : List UInt8 := [0x48,0x8d,0x7c,0x24,0x78,0x48,0x89,0xde]

def finalizerSetupEffect (s : RamState) : Effect :=
  { rip := 0x101747
    writes := [
      ⟨(.reg 7 : Operand 64), rspOf s + 120⟩,
      ⟨(.reg 6 : Operand 64), s.regValue .rbx⟩] }

theorem finalizerSetup_code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x10173f finalizerSetupBytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0x173f finalizerSetupBytes
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 800000 in
theorem finalizerSetup_run [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s ↦ s.RIP = 0x10173f)
      (codeRange 0x10173f finalizerSetupBytes) (Effect.post finalizerSetupEffect) := by
  advance_begin (lea_r64_effect_step 0x10173f 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d8 120)) (by decide +kernel) rfl rfl)
  case next => exact fun _ _ ↦ boundary_ne_program outside (inProgram_of_textOffset 0x1744 (by decide))
  advance_then (mov_r64_r64_effect_step 0x101744 0x48 0xde (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10173f finalizerSetupBytes 5 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0x1747 (by decide))⟩
  advance_finish [finalizerSetupEffect]

end Hkdf.Proofs.Standard.Finalize
