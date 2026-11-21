import P256.Proofs.Sec1.Affine.State
import P256.Proofs.SignatureFromDer.Parser.ReadSlice.Execution
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Instructions.MovzxByte
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compact.Normalize

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SignatureFromDer.Parser.ReadSlice
open P256.Proofs.Common.Instructions.MovzxByte

def negativeBytes : List UInt8 := [0x4c,0x8d,0xbc,0x24,0xc8,0x0,0x0,0x0,0x48,0x8d,0xb4,0x24,0x58,0x1,0x0,0x0,0x4c,0x89,0xff]

def negativeEffect (s : RamState) : Effect :=
  { rip := 0x11036b
    writes := [⟨(.reg 15 : Operand 64), stackPtr s + 200⟩,
      ⟨(.reg 6 : Operand 64), stackPtr s + 344⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 200⟩] }

theorem negative_setup [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s => s.RIP = 0x110358) (codeRange 0x110358 negativeBytes) negativeEffect := by
  unfold negativeBytes
  slice_run_begin (show StepEffect _ _ (leaR64Effect 0x110358 15 (.sib 4 none 0 (.d32 200))) from
    lea_r64_effect_step 0x110358 0x4c (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 200)) (by decide) rfl rfl)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10360 (by decide))
  slice_run_then (show StepEffect _ _ (leaR64Effect 0x110360 6 (.sib 4 none 0 (.d32 344))) from
    lea_r64_effect_step 0x110360 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 344)) (by decide) rfl rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x110358) 8 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10368 (by decide))
  slice_run_then (show StepEffect _ _ (movR64R64Effect 0x110368 7 15) from
    mov_r64_r64_effect_step 0x110368 0x4c 0xff (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x110358) 16 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x1036b (by decide))
  apply P256.Proofs.Common.Field.AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · x86_norm [negativeEffect]
  · x86_norm [negativeEffect] <;> rfl
  · intro f; cases f <;> x86_norm [negativeEffect]
  · x86_norm [negativeEffect]

def firstDecodeBytes : List UInt8 := [0x48,0x8d,0xbc,0x24,0x40,0x2,0x0,0x0,0x4c,0x89,0xe6]

def firstDecodeEffect (s : RamState) : Effect :=
  { rip := 0x1103c3
    writes := [⟨(.reg 7 : Operand 64), stackPtr s + 576⟩,
      ⟨(.reg 6 : Operand 64), (Operand.reg 12 : Operand 64).read s⟩] }

theorem firstDecode_setup [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s => s.RIP = 0x1103b8) (codeRange 0x1103b8 firstDecodeBytes) firstDecodeEffect := by
  unfold firstDecodeBytes
  slice_run_begin (show StepEffect _ _ (leaR64Effect 0x1103b8 7 (.sib 4 none 0 (.d32 576))) from
    lea_r64_effect_step 0x1103b8 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 576)) (by decide) rfl rfl)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x103c0 (by decide))
  slice_run_then (show StepEffect _ _ (movR64R64Effect 0x1103c0 6 12) from
    mov_r64_r64_effect_step 0x1103c0 0x4c 0xe6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x1103b8) 8 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x103c3 (by decide))
  apply P256.Proofs.Common.Field.AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · x86_norm [firstDecodeEffect]
  · x86_norm [firstDecodeEffect] <;> rfl
  · intro f; cases f <;> x86_norm [firstDecodeEffect]
  · x86_norm [firstDecodeEffect]

def secondDecodeBytes : List UInt8 := [0x48,0x8d,0xbc,0x24,0x58,0x1,0x0,0x0,0x4c,0x89,0xfe]

def secondDecodeEffect (s : RamState) : Effect :=
  { rip := 0x1103d3
    writes := [⟨(.reg 7 : Operand 64), stackPtr s + 344⟩,
      ⟨(.reg 6 : Operand 64), (Operand.reg 15 : Operand 64).read s⟩] }

theorem secondDecode_setup [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s => s.RIP = 0x1103c8) (codeRange 0x1103c8 secondDecodeBytes) secondDecodeEffect := by
  unfold secondDecodeBytes
  slice_run_begin (show StepEffect _ _ (leaR64Effect 0x1103c8 7 (.sib 4 none 0 (.d32 344))) from
    lea_r64_effect_step 0x1103c8 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 344)) (by decide) rfl rfl)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x103d0 (by decide))
  slice_run_then (show StepEffect _ _ (movR64R64Effect 0x1103d0 6 15) from
    mov_r64_r64_effect_step 0x1103d0 0x4c 0xfe (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x1103c8) 8 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x103d3 (by decide))
  apply P256.Proofs.Common.Field.AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · x86_norm [secondDecodeEffect]
  · x86_norm [secondDecodeEffect] <;> rfl
  · intro f; cases f <;> x86_norm [secondDecodeEffect]
  · x86_norm [secondDecodeEffect]

def minimumBytes : List UInt8 := [0x48,0x8d,0xbc,0x24,0xa0,0x2,0x0,0x0,0xf,0xb6,0xc8,0x4c,0x89,0xe6,0x4c,0x89,0xfa]

def minimumEffect (s : RamState) : Effect :=
  { rip := 0x1104fb
    writes := [⟨(.reg 7 : Operand 64), stackPtr s + 672⟩,
      ⟨(.reg 1 : Operand 64), (((Operand.reg 0 : Operand 64).read s).setWidth 8).setWidth 64⟩,
      ⟨(.reg 6 : Operand 64), (Operand.reg 12 : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), (Operand.reg 15 : Operand 64).read s⟩] }

theorem minimum_setup [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s => s.RIP = 0x1104ea) (codeRange 0x1104ea minimumBytes) minimumEffect := by
  unfold minimumBytes
  slice_run_begin (show StepEffect _ _ (leaR64Effect 0x1104ea 7 (.sib 4 none 0 (.d32 672))) from
    lea_r64_effect_step 0x1104ea 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 672)) (by decide) rfl rfl)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x104f2 (by decide))
  slice_run_then (show StepEffect _ _ (movzxR32R8Effect 0x1104f2 3 1 0) from
    movzx_r32_r8_effect_step 0x1104f2 0xc8 rfl (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x1104ea) 8 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x104f5 (by decide))
  slice_run_then (show StepEffect _ _ (movR64R64Effect 0x1104f5 6 12) from
    mov_r64_r64_effect_step 0x1104f5 0x4c 0xe6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x1104ea) 11 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x104f8 (by decide))
  slice_run_then (show StepEffect _ _ (movR64R64Effect 0x1104f8 2 15) from
    mov_r64_r64_effect_step 0x1104f8 0x4c 0xfa (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x1104ea) 14 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x104fb (by decide))
  apply P256.Proofs.Common.Field.AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · x86_norm [minimumEffect]
  · x86_norm [minimumEffect] <;> rfl
  · intro f; cases f <;> x86_norm [minimumEffect]
  · x86_norm [minimumEffect]

def finalXBytes : List UInt8 := [0x48,0x8d,0x7c,0x24,0x60,0x48,0x89,0xc6,0x89,0xe9]

def finalXEffect (s : RamState) : Effect :=
  { rip := 0x110589
    writes := [⟨(.reg 7 : Operand 64), stackPtr s + 96⟩,
      ⟨(.reg 6 : Operand 64), (Operand.reg 0 : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), (((Operand.reg 5 : Operand 64).read s).setWidth 32).setWidth 64⟩] }

theorem finalX_setup [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s => s.RIP = 0x11057f) (codeRange 0x11057f finalXBytes) finalXEffect := by
  unfold finalXBytes
  slice_run_begin (show StepEffect _ _ (leaR64Effect 0x11057f 7 (.sib 4 none 0 (.d8 96))) from
    lea_r64_effect_step 0x11057f 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 96)) (by decide) rfl rfl)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10584 (by decide))
  slice_run_then (show StepEffect _ _ (movR64R64Effect 0x110584 6 0) from
    mov_r64_r64_effect_step 0x110584 0x48 0xc6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x11057f) 5 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10587 (by decide))
  slice_run_then (mov_r32_r32_effect_step 0x110587 0xe9 rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x11057f) 8 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10589 (by decide))
  apply P256.Proofs.Common.Field.AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · x86_norm [finalXEffect]
  · x86_norm [finalXEffect] <;> rfl
  · intro f; cases f <;> x86_norm [finalXEffect]
  · x86_norm [finalXEffect]

def finalYBytes : List UInt8 := [0x48,0x8d,0xb4,0x24,0xc8,0x0,0x0,0x0,0x48,0x8d,0x54,0x24,0x30,0x48,0x8d,0xbc,0x24,0x80,0x0,0x0,0x0,0x89,0xe9]

def finalYEffect (s : RamState) : Effect :=
  { rip := 0x1105a5
    writes := [⟨(.reg 6 : Operand 64), stackPtr s + 200⟩,
      ⟨(.reg 2 : Operand 64), stackPtr s + 48⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 128⟩,
      ⟨(.reg 1 : Operand 64), (((Operand.reg 5 : Operand 64).read s).setWidth 32).setWidth 64⟩] }

theorem finalY_setup [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s => s.RIP = 0x11058e) (codeRange 0x11058e finalYBytes) finalYEffect := by
  unfold finalYBytes
  slice_run_begin (show StepEffect _ _ (leaR64Effect 0x11058e 6 (.sib 4 none 0 (.d32 200))) from
    lea_r64_effect_step 0x11058e 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 200)) (by decide) rfl rfl)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10596 (by decide))
  slice_run_then (show StepEffect _ _ (leaR64Effect 0x110596 2 (.sib 4 none 0 (.d8 48))) from
    lea_r64_effect_step 0x110596 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 48)) (by decide) rfl rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x11058e) 8 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x1059b (by decide))
  slice_run_then (show StepEffect _ _ (leaR64Effect 0x11059b 7 (.sib 4 none 0 (.d32 128))) from
    lea_r64_effect_step 0x11059b 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 128)) (by decide) rfl rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x11058e) 13 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x105a3 (by decide))
  slice_run_then (mov_r32_r32_effect_step 0x1105a3 0xe9 rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x11058e) 21 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x105a5 (by decide))
  apply P256.Proofs.Common.Field.AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · x86_norm [finalYEffect]
  · x86_norm [finalYEffect] <;> rfl
  · intro f; cases f <;> x86_norm [finalYEffect]
  · x86_norm [finalYEffect]

end P256.Proofs.Sec1.Affine.Compact.Normalize
