import P256.Proofs.Verifying.Core.Combine.Interface
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.Field.Montgomery.Schoolbook.Compose
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Combine

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame
open P256.Proofs.Common.Field (AdvanceTriple)

def generatorBytes : List UInt8 :=
  [0x48,0x8d,0x84,0x24,0x40,0x02,0x00,0x00,0xb9,0x0c,0x00,0x00,0x00,0x48,0x89,0xc7,0x48,0xc7,0xc6,0xc8,0x2a,0x20,0x00]

def generatorEffect (s : RamState) : Effect :=
  { rip := 0x10dd80
    writes := [⟨(.reg 0 : Operand 64), rspOf s+576⟩,
      ⟨(.reg 1 : Operand 64), 12⟩,
      ⟨(.reg 7 : Operand 64), rspOf s+576⟩,
      ⟨(.reg 6 : Operand 64), 0x202ac8⟩] }

theorem generator_setup [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10dd69)
      (codeRange 0x10dd69 generatorBytes) (Effect.post generatorEffect) := by
  advance_begin (lea_r64_effect_step 0x10dd69 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 576)) (by decide) rfl rfl)
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0xdd71 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10dd71 0xb9 (by decide) 12)
  case sub => exact codeRange_slice_subset 0x10dd69 generatorBytes 8 5
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xdd76 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10dd76 0x48 0xc7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10dd69 generatorBytes 13 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xdd79 (by decide))⟩
  advance_then (mov_r64_imm32_effect_step 0x10dd79 0x48 0xc6 (by simp [RexWPrefix]) rfl rfl 0x202ac8)
  case sub => exact codeRange_slice_subset 0x10dd69 generatorBytes 16 7
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xdd80 (by decide))⟩
  advance_finish [generatorEffect]

def pointBytes : List UInt8 :=
  [0x48,0x89,0xe2,0x48,0x8d,0xb4,0x24,0xe8,0x03,0x00,0x00,0xb9,0x0c,0x00,0x00,0x00,0x48,0x89,0xd7]

def pointEffect (s : RamState) : Effect :=
  { rip := 0x10ddd6
    writes := [⟨(.reg 2 : Operand 64), rspOf s⟩,
      ⟨(.reg 1 : Operand 64), 12⟩,
      ⟨(.reg 7 : Operand 64), rspOf s⟩,
      ⟨(.reg 6 : Operand 64), rspOf s+1000⟩] }

theorem point_setup [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10ddc3)
      (codeRange 0x10ddc3 pointBytes) (Effect.post pointEffect) := by
  advance_begin (mov_r64_r64_effect_step 0x10ddc3 0x48 0xe2 (by simp [RexWPrefix]) rfl)
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0xddc6 (by decide))
  advance_then (lea_r64_effect_step 0x10ddc6 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d32 1000)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10ddc3 pointBytes 3 8
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xddce (by decide))⟩
  advance_then (mov_r32_imm32_effect_step 0x10ddce 0xb9 (by decide) 12)
  case sub => exact codeRange_slice_subset 0x10ddc3 pointBytes 11 5
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xddd3 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10ddd3 0x48 0xd7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10ddc3 pointBytes 16 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xddd6 (by decide))⟩
  advance_finish [pointEffect]

def firstBytes : List UInt8 :=
  [0x4c,0x8d,0x84,0x24,0x80,0x00,0x00,0x00,0xb9,0x10,0x00,0x00,0x00,0x4c,0x89,0xc7,0x48,0x89,0xc6]

def firstEffect (s : RamState) : Effect :=
  { rip := 0x10de20
    writes := [⟨(.reg 8 : Operand 64), rspOf s+128⟩,
      ⟨(.reg 1 : Operand 64), 16⟩,
      ⟨(.reg 7 : Operand 64), rspOf s+128⟩,
      ⟨(.reg 6 : Operand 64), (Operand.reg 0 : Operand 64).read s⟩] }

theorem first_setup [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10de0d)
      (codeRange 0x10de0d firstBytes) (Effect.post firstEffect) := by
  advance_begin (lea_r64_effect_step 0x10de0d 0x4c (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 128)) (by decide) rfl rfl)
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0xde15 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10de15 0xb9 (by decide) 16)
  case sub => exact codeRange_slice_subset 0x10de0d firstBytes 8 5
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xde1a (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10de1a 0x4c 0xc7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10de0d firstBytes 13 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xde1d (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10de1d 0x48 0xc6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10de0d firstBytes 16 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xde20 (by decide))⟩
  advance_finish [firstEffect]

def secondBytes : List UInt8 :=
  [0x48,0x8d,0xbc,0x24,0x00,0x01,0x00,0x00,0xb9,0x10,0x00,0x00,0x00,0x48,0x89,0xd6]

def secondEffect (s : RamState) : Effect :=
  { rip := 0x10de33
    writes := [⟨(.reg 7 : Operand 64), rspOf s+256⟩,
      ⟨(.reg 1 : Operand 64), 16⟩,
      ⟨(.reg 6 : Operand 64), (Operand.reg 2 : Operand 64).read s⟩] }

theorem second_setup [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10de23)
      (codeRange 0x10de23 secondBytes) (Effect.post secondEffect) := by
  advance_begin (lea_r64_effect_step 0x10de23 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 256)) (by decide) rfl rfl)
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0xde2b (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10de2b 0xb9 (by decide) 16)
  case sub => exact codeRange_slice_subset 0x10de23 secondBytes 8 5
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xde30 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10de30 0x48 0xd6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10de23 secondBytes 13 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xde33 (by decide))⟩
  advance_finish [secondEffect]

def callBytes : List UInt8 :=
  [0x48,0x89,0xe7,0x4c,0x89,0xc6]

def callEffect (s : RamState) : Effect :=
  { rip := 0x10de3c
    writes := [⟨(.reg 7 : Operand 64), rspOf s⟩,
      ⟨(.reg 6 : Operand 64), (Operand.reg 8 : Operand 64).read s⟩] }

theorem call_setup [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10de36)
      (codeRange 0x10de36 callBytes) (Effect.post callEffect) := by
  advance_begin (mov_r64_r64_effect_step 0x10de36 0x48 0xe7 (by simp [RexWPrefix]) rfl)
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0xde39 (by decide))
  advance_then (mov_r64_r64_effect_step 0x10de39 0x4c 0xc6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10de36 callBytes 3 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xde3c (by decide))⟩
  advance_finish [callEffect]

end P256.Proofs.Verifying.Core.Combine
