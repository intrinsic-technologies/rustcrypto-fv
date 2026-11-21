import P256.Proofs.Sec1.Affine.State
import P256.Proofs.SignatureFromDer.Parser.ReadSlice.Execution
import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Triple
import P256.Proofs.Common.Instructions.LegacyLoad

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compressed.Finish

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SignatureFromDer.Parser.ReadSlice
open P256.Proofs.Common.Instructions.LegacyLoad

structure SelectFirstPre (s : RamState) : Prop where
  rip : s.RIP = 0x11015b
  readable : MemReadable s (stackPtr s + 88) 4

def selectFirstBytes : List UInt8 :=
  [0x8b, 0x6c, 0x24, 0x58, 0x48, 0x8d, 0xbc, 0x24, 0x78, 1, 0, 0,
   0x48, 0x89, 0xc6, 0x89, 0xe9]

def selectFirstEffect (s : RamState) : Effect :=
  { rip := 0x11016c
    writes := [⟨(.reg 5 : Operand 64), (memLoad s.external (stackPtr s + 88) 32).setWidth 64⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 376⟩,
      ⟨(.reg 6 : Operand 64), s.regValue .rax⟩,
      ⟨(.reg 1 : Operand 64), (memLoad s.external (stackPtr s + 88) 32).setWidth 64⟩] }

attribute [local x86_compose] movR32M32LegacyEffect

set_option maxHeartbeats 800000 in
theorem select_first_setup [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary SelectFirstPre (codeRange 0x11015b selectFirstBytes) selectFirstEffect := by
  unfold selectFirstBytes
  slice_run_begin (show StepEffect _ _ (movR32M32LegacyEffect 0x11015b 5 (.sib 4 none 0 (.d8 88))) from
    mov_r32_m32_legacy_effect_step 0x11015b 5 (.sib 4 none 0 (.d8 88)) (by decide) rfl rfl)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x1015f (by decide))
  slice_run_then (show StepEffect _ _ (leaR64Effect 0x11015f 7 (.sib 4 none 0 (.d32 376))) from
    lea_r64_effect_step 0x11015f 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 376))
      (by constructor <;> decide) rfl rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x11015b) 4 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10167 (by decide))
  slice_run_then (show StepEffect _ _ (movR64R64Effect 0x110167 6 0) from
    mov_r64_r64_effect_step 0x110167 0x48 0xc6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x11015b) 12 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x1016a (by decide))
  slice_run_then (mov_r32_r32_effect_step 0x11016a 0xe9 rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x11015b) 15 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x1016c (by decide))
  apply P256.Proofs.Common.Field.AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · x86_norm [selectFirstEffect]
  · x86_norm [selectFirstEffect]
    constructor
    · rfl
    · rw [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)]
      rfl
  · intro f; cases f <;> x86_norm [selectFirstEffect]
  · x86_norm [selectFirstEffect]


def selectSecondBytes : List UInt8 :=
  [0x48,0x8d,0xb4,0x24,0x80,0,0,0,0x48,0x8d,0x54,0x24,0x30,
   0x48,0x8d,0xbc,0x24,0x98,1,0,0,0x89,0xe9]

def selectSecondEffect (s : RamState) : Effect :=
  { rip := 0x110188
    writes := [⟨(.reg 6 : Operand 64), stackPtr s + 128⟩,
      ⟨(.reg 2 : Operand 64), stackPtr s + 48⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 408⟩,
      ⟨(.reg 1 : Operand 64), ((s.regValue .rbp).setWidth 32).setWidth 64⟩] }

set_option maxHeartbeats 800000 in
theorem select_second_setup [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s => s.RIP = 0x110171)
      (codeRange 0x110171 selectSecondBytes) selectSecondEffect := by
  unfold selectSecondBytes
  slice_run_begin (show StepEffect _ _ (leaR64Effect 0x110171 6 (.sib 4 none 0 (.d32 128))) from
    lea_r64_effect_step 0x110171 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 128))
      (by constructor <;> decide) rfl rfl)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10179 (by decide))
  slice_run_then (show StepEffect _ _ (leaR64Effect 0x110179 2 (.sib 4 none 0 (.d8 48))) from
    lea_r64_effect_step 0x110179 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 48))
      (by constructor <;> decide) rfl rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x110171) 8 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x1017e (by decide))
  slice_run_then (show StepEffect _ _ (leaR64Effect 0x11017e 7 (.sib 4 none 0 (.d32 408))) from
    lea_r64_effect_step 0x11017e 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 408))
      (by constructor <;> decide) rfl rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x110171) 13 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10186 (by decide))
  slice_run_then (mov_r32_r32_effect_step 0x110186 0xe9 rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x110171) 21 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10188 (by decide))
  apply P256.Proofs.Common.Field.AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · x86_norm [selectSecondEffect]
  · x86_norm [selectSecondEffect] <;> rfl
  · intro f; cases f <;> x86_norm [selectSecondEffect]
  · x86_norm [selectSecondEffect]

end P256.Proofs.Sec1.Affine.Compressed.Finish
