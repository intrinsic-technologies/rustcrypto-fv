import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Program.Code

import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Verifying.Combination.Table

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def firstCopySetupBytes : List UInt8 :=
  [0x4c, 0x8d, 0xb4, 0x24, 0x68, 0x3, 0x0, 0x0, 0xb9, 0xc, 0x0, 0x0, 0x0, 0x4c, 0x89, 0xf7, 0x48, 0x89, 0xc6]

def firstCopySetupEffect (s : RamState) : Effect :=
  { rip := 0x10b024
    writes := [⟨(Operand.reg 14 : Operand 64), stackPtr s + 872⟩,
      ⟨(Operand.reg 1 : Operand 64), 12⟩,
      ⟨(Operand.reg 7 : Operand 64), stackPtr s + 872⟩,
      ⟨(Operand.reg 6 : Operand 64), s.regValue .rax⟩] }

theorem firstCopySetup_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10b011)
      (codeRange 0x10b011 firstCopySetupBytes) (Effect.post firstCopySetupEffect) := by
  advance_begin (lea_r64_effect_step 0x10b011 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 872)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0xb019 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10b019 0xb9 (by decide) 12)
  case sub => exact codeRange_slice_subset 0x10b011 firstCopySetupBytes 8 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xb01e (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10b01e 0x4c 0xf7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10b011 firstCopySetupBytes 13 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xb021 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10b021 0x48 0xc6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10b011 firstCopySetupBytes 16 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xb024 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [firstCopySetupEffect]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [firstCopySetupEffect]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [firstCopySetupEffect]
  · x86_norm [firstCopySetupEffect]
    all_goals (repeat first | constructor | rfl)

def doubleCopySetupBytes : List UInt8 :=
  [0x4c, 0x8d, 0xbc, 0x24, 0xc8, 0x3, 0x0, 0x0, 0xb9, 0xc, 0x0, 0x0, 0x0, 0x4c, 0x89, 0xff, 0x48, 0x89, 0xc6]

def doubleCopySetupEffect (s : RamState) : Effect :=
  { rip := 0x10b03a
    writes := [⟨(Operand.reg 15 : Operand 64), stackPtr s + 968⟩,
      ⟨(Operand.reg 1 : Operand 64), 12⟩,
      ⟨(Operand.reg 7 : Operand 64), stackPtr s + 968⟩,
      ⟨(Operand.reg 6 : Operand 64), s.regValue .rax⟩] }

theorem doubleCopySetup_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10b027)
      (codeRange 0x10b027 doubleCopySetupBytes) (Effect.post doubleCopySetupEffect) := by
  advance_begin (lea_r64_effect_step 0x10b027 0x4c (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 968)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0xb02f (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10b02f 0xb9 (by decide) 12)
  case sub => exact codeRange_slice_subset 0x10b027 doubleCopySetupBytes 8 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xb034 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10b034 0x4c 0xff (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10b027 doubleCopySetupBytes 13 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xb037 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10b037 0x48 0xc6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10b027 doubleCopySetupBytes 16 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xb03a (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [doubleCopySetupEffect]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [doubleCopySetupEffect]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [doubleCopySetupEffect]
  · x86_norm [doubleCopySetupEffect]
    all_goals (repeat first | constructor | rfl)

def doubledCopySetupBytes : List UInt8 :=
  [0x4c, 0x8d, 0xa4, 0x24, 0x8, 0x3, 0x0, 0x0, 0xb9, 0xc, 0x0, 0x0, 0x0, 0x4c, 0x89, 0xe7, 0x4c, 0x89, 0xfe]

def doubledCopySetupEffect (s : RamState) : Effect :=
  { rip := 0x10b058
    writes := [⟨(Operand.reg 12 : Operand 64), stackPtr s + 776⟩,
      ⟨(Operand.reg 1 : Operand 64), 12⟩,
      ⟨(Operand.reg 7 : Operand 64), stackPtr s + 776⟩,
      ⟨(Operand.reg 6 : Operand 64), s.regValue .r15⟩] }

theorem doubledCopySetup_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10b045)
      (codeRange 0x10b045 doubledCopySetupBytes) (Effect.post doubledCopySetupEffect) := by
  advance_begin (lea_r64_effect_step 0x10b045 0x4c (by simp [RexWPrefix]) 4 (.sib 4 none 0 (.d32 776)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0xb04d (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10b04d 0xb9 (by decide) 12)
  case sub => exact codeRange_slice_subset 0x10b045 doubledCopySetupBytes 8 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xb052 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10b052 0x4c 0xe7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10b045 doubledCopySetupBytes 13 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xb055 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10b055 0x4c 0xfe (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10b045 doubledCopySetupBytes 16 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xb058 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [doubledCopySetupEffect]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [doubledCopySetupEffect]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [doubledCopySetupEffect]
  · x86_norm [doubledCopySetupEffect]
    all_goals (repeat first | constructor | rfl)

def tableStartSetupBytes : List UInt8 :=
  [0x4c, 0x8d, 0x7c, 0x24, 0x8, 0xb9, 0xc, 0x0, 0x0, 0x0, 0x4c, 0x89, 0xff, 0x4c, 0x89, 0xf6]

def tableStartSetupEffect (s : RamState) : Effect :=
  { rip := 0x10b06b
    writes := [⟨(Operand.reg 15 : Operand 64), stackPtr s + 8⟩,
      ⟨(Operand.reg 1 : Operand 64), 12⟩,
      ⟨(Operand.reg 7 : Operand 64), stackPtr s + 8⟩,
      ⟨(Operand.reg 6 : Operand 64), s.regValue .r14⟩] }

theorem tableStartSetup_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10b05b)
      (codeRange 0x10b05b tableStartSetupBytes) (Effect.post tableStartSetupEffect) := by
  advance_begin (lea_r64_effect_step 0x10b05b 0x4c (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0xb060 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10b060 0xb9 (by decide) 12)
  case sub => exact codeRange_slice_subset 0x10b05b tableStartSetupBytes 5 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xb065 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10b065 0x4c 0xff (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10b05b tableStartSetupBytes 10 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xb068 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10b068 0x4c 0xf6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10b05b tableStartSetupBytes 13 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xb06b (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [tableStartSetupEffect]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [tableStartSetupEffect]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [tableStartSetupEffect]
  · x86_norm [tableStartSetupEffect]
    all_goals (repeat first | constructor | rfl)

def tableCopySetup1Bytes : List UInt8 :=
  [0x48, 0x8d, 0x7c, 0x24, 0x68, 0xb9, 0xc, 0x0, 0x0, 0x0, 0x4c, 0x89, 0xf6]

def tableCopySetup1Effect (s : RamState) : Effect :=
  { rip := 0x10b086
    writes := [⟨(Operand.reg 7 : Operand 64), stackPtr s + 104⟩,
      ⟨(Operand.reg 1 : Operand 64), 12⟩,
      ⟨(Operand.reg 6 : Operand 64), s.regValue .r14⟩] }

theorem tableCopySetup1_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10b079)
      (codeRange 0x10b079 tableCopySetup1Bytes) (Effect.post tableCopySetup1Effect) := by
  advance_begin (lea_r64_effect_step 0x10b079 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 104)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0xb07e (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10b07e 0xb9 (by decide) 12)
  case sub => exact codeRange_slice_subset 0x10b079 tableCopySetup1Bytes 5 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xb083 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10b083 0x4c 0xf6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10b079 tableCopySetup1Bytes 10 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xb086 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [tableCopySetup1Effect]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [tableCopySetup1Effect]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [tableCopySetup1Effect]
  · x86_norm [tableCopySetup1Effect]
    all_goals (repeat first | constructor | rfl)

def tableCopySetup2Bytes : List UInt8 :=
  [0x48, 0x8d, 0xbc, 0x24, 0xc8, 0x0, 0x0, 0x0, 0xb9, 0xc, 0x0, 0x0, 0x0, 0x4c, 0x89, 0xf6]

def tableCopySetup2Effect (s : RamState) : Effect :=
  { rip := 0x10b0a4
    writes := [⟨(Operand.reg 7 : Operand 64), stackPtr s + 200⟩,
      ⟨(Operand.reg 1 : Operand 64), 12⟩,
      ⟨(Operand.reg 6 : Operand 64), s.regValue .r14⟩] }

theorem tableCopySetup2_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10b094)
      (codeRange 0x10b094 tableCopySetup2Bytes) (Effect.post tableCopySetup2Effect) := by
  advance_begin (lea_r64_effect_step 0x10b094 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 200)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0xb09c (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10b09c 0xb9 (by decide) 12)
  case sub => exact codeRange_slice_subset 0x10b094 tableCopySetup2Bytes 8 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xb0a1 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10b0a1 0x4c 0xf6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10b094 tableCopySetup2Bytes 13 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xb0a4 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [tableCopySetup2Effect]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [tableCopySetup2Effect]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [tableCopySetup2Effect]
  · x86_norm [tableCopySetup2Effect]
    all_goals (repeat first | constructor | rfl)

def tableCopySetup3Bytes : List UInt8 :=
  [0x48, 0x8d, 0xbc, 0x24, 0x28, 0x1, 0x0, 0x0, 0xb9, 0xc, 0x0, 0x0, 0x0, 0x4c, 0x89, 0xf6]

def tableCopySetup3Effect (s : RamState) : Effect :=
  { rip := 0x10b0c2
    writes := [⟨(Operand.reg 7 : Operand 64), stackPtr s + 296⟩,
      ⟨(Operand.reg 1 : Operand 64), 12⟩,
      ⟨(Operand.reg 6 : Operand 64), s.regValue .r14⟩] }

theorem tableCopySetup3_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10b0b2)
      (codeRange 0x10b0b2 tableCopySetup3Bytes) (Effect.post tableCopySetup3Effect) := by
  advance_begin (lea_r64_effect_step 0x10b0b2 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 296)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0xb0ba (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10b0ba 0xb9 (by decide) 12)
  case sub => exact codeRange_slice_subset 0x10b0b2 tableCopySetup3Bytes 8 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xb0bf (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10b0bf 0x4c 0xf6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10b0b2 tableCopySetup3Bytes 13 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xb0c2 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [tableCopySetup3Effect]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [tableCopySetup3Effect]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [tableCopySetup3Effect]
  · x86_norm [tableCopySetup3Effect]
    all_goals (repeat first | constructor | rfl)

def tableCopySetup4Bytes : List UInt8 :=
  [0x48, 0x8d, 0xbc, 0x24, 0x88, 0x1, 0x0, 0x0, 0xb9, 0xc, 0x0, 0x0, 0x0, 0x4c, 0x89, 0xf6]

def tableCopySetup4Effect (s : RamState) : Effect :=
  { rip := 0x10b0e0
    writes := [⟨(Operand.reg 7 : Operand 64), stackPtr s + 392⟩,
      ⟨(Operand.reg 1 : Operand 64), 12⟩,
      ⟨(Operand.reg 6 : Operand 64), s.regValue .r14⟩] }

theorem tableCopySetup4_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10b0d0)
      (codeRange 0x10b0d0 tableCopySetup4Bytes) (Effect.post tableCopySetup4Effect) := by
  advance_begin (lea_r64_effect_step 0x10b0d0 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 392)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0xb0d8 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10b0d8 0xb9 (by decide) 12)
  case sub => exact codeRange_slice_subset 0x10b0d0 tableCopySetup4Bytes 8 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xb0dd (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10b0dd 0x4c 0xf6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10b0d0 tableCopySetup4Bytes 13 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xb0e0 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [tableCopySetup4Effect]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [tableCopySetup4Effect]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [tableCopySetup4Effect]
  · x86_norm [tableCopySetup4Effect]
    all_goals (repeat first | constructor | rfl)

def tableCopySetup5Bytes : List UInt8 :=
  [0x48, 0x8d, 0xbc, 0x24, 0xe8, 0x1, 0x0, 0x0, 0xb9, 0xc, 0x0, 0x0, 0x0, 0x4c, 0x89, 0xf6]

def tableCopySetup5Effect (s : RamState) : Effect :=
  { rip := 0x10b0fe
    writes := [⟨(Operand.reg 7 : Operand 64), stackPtr s + 488⟩,
      ⟨(Operand.reg 1 : Operand 64), 12⟩,
      ⟨(Operand.reg 6 : Operand 64), s.regValue .r14⟩] }

theorem tableCopySetup5_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10b0ee)
      (codeRange 0x10b0ee tableCopySetup5Bytes) (Effect.post tableCopySetup5Effect) := by
  advance_begin (lea_r64_effect_step 0x10b0ee 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 488)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0xb0f6 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10b0f6 0xb9 (by decide) 12)
  case sub => exact codeRange_slice_subset 0x10b0ee tableCopySetup5Bytes 8 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xb0fb (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10b0fb 0x4c 0xf6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10b0ee tableCopySetup5Bytes 13 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xb0fe (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [tableCopySetup5Effect]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [tableCopySetup5Effect]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [tableCopySetup5Effect]
  · x86_norm [tableCopySetup5Effect]
    all_goals (repeat first | constructor | rfl)

def tableCopySetup6Bytes : List UInt8 :=
  [0x48, 0x8d, 0xbc, 0x24, 0x48, 0x2, 0x0, 0x0, 0xb9, 0xc, 0x0, 0x0, 0x0, 0x4c, 0x89, 0xf6]

def tableCopySetup6Effect (s : RamState) : Effect :=
  { rip := 0x10b11c
    writes := [⟨(Operand.reg 7 : Operand 64), stackPtr s + 584⟩,
      ⟨(Operand.reg 1 : Operand 64), 12⟩,
      ⟨(Operand.reg 6 : Operand 64), s.regValue .r14⟩] }

theorem tableCopySetup6_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10b10c)
      (codeRange 0x10b10c tableCopySetup6Bytes) (Effect.post tableCopySetup6Effect) := by
  advance_begin (lea_r64_effect_step 0x10b10c 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 584)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0xb114 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10b114 0xb9 (by decide) 12)
  case sub => exact codeRange_slice_subset 0x10b10c tableCopySetup6Bytes 8 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xb119 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10b119 0x4c 0xf6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10b10c tableCopySetup6Bytes 13 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xb11c (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [tableCopySetup6Effect]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [tableCopySetup6Effect]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [tableCopySetup6Effect]
  · x86_norm [tableCopySetup6Effect]
    all_goals (repeat first | constructor | rfl)

def tableCopySetup7Bytes : List UInt8 :=
  [0x48, 0x8d, 0xbc, 0x24, 0xa8, 0x2, 0x0, 0x0, 0xb9, 0xc, 0x0, 0x0, 0x0, 0x4c, 0x89, 0xf6]

def tableCopySetup7Effect (s : RamState) : Effect :=
  { rip := 0x10b13a
    writes := [⟨(Operand.reg 7 : Operand 64), stackPtr s + 680⟩,
      ⟨(Operand.reg 1 : Operand 64), 12⟩,
      ⟨(Operand.reg 6 : Operand 64), s.regValue .r14⟩] }

theorem tableCopySetup7_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10b12a)
      (codeRange 0x10b12a tableCopySetup7Bytes) (Effect.post tableCopySetup7Effect) := by
  advance_begin (lea_r64_effect_step 0x10b12a 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 680)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0xb132 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10b132 0xb9 (by decide) 12)
  case sub => exact codeRange_slice_subset 0x10b12a tableCopySetup7Bytes 8 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xb137 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10b137 0x4c 0xf6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10b12a tableCopySetup7Bytes 13 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xb13a (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [tableCopySetup7Effect]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [tableCopySetup7Effect]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [tableCopySetup7Effect]
  · x86_norm [tableCopySetup7Effect]
    all_goals (repeat first | constructor | rfl)

def outputCopySetupBytes : List UInt8 :=
  [0xba, 0x0, 0x3, 0x0, 0x0, 0x48, 0x89, 0xdf, 0x4c, 0x89, 0xfe]

def outputCopySetupEffect (s : RamState) : Effect :=
  { rip := 0x10b153
    writes := [⟨(Operand.reg 2 : Operand 64), 768⟩,
      ⟨(Operand.reg 7 : Operand 64), s.regValue .rbx⟩,
      ⟨(Operand.reg 6 : Operand 64), s.regValue .r15⟩] }

theorem outputCopySetup_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10b148)
      (codeRange 0x10b148 outputCopySetupBytes) (Effect.post outputCopySetupEffect) := by
  advance_begin (mov_r32_imm32_effect_step 0x10b148 0xba (by decide) 768)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0xb14d (by decide))
  advance_then (mov_r64_r64_effect_step 0x10b14d 0x48 0xdf (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10b148 outputCopySetupBytes 5 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xb150 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10b150 0x4c 0xfe (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10b148 outputCopySetupBytes 8 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xb153 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [outputCopySetupEffect]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [outputCopySetupEffect]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [outputCopySetupEffect]
  · x86_norm [outputCopySetupEffect]
    all_goals (repeat first | constructor | rfl)


end P256.Proofs.Verifying.Combination.Table
