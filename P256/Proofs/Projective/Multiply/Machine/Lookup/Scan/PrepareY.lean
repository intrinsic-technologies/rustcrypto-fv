import P256.Proofs.Projective.Multiply.Machine.Lookup.Interface
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.Instructions.MovzxByte
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Add.Generated.Imm32.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Projective.Multiply.Machine.Lookup.Scanning

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def prepareY0Bytes : List UInt8 := [0x49,0x8d,0x55,0x20,0x4c,0x89,0xf7,0x48,0x8d,0x74,0x24,0x30,0x89,0xd9]

def prepareY0Effect (s : RamState) : Effect :=
  { rip := 0x104522
    writes := [⟨(Operand.reg 2 : Operand 64), (s.regValue .r13) + 32⟩,
      ⟨(Operand.reg 7 : Operand 64), s.regValue .r14⟩,
      ⟨(Operand.reg 6 : Operand 64), (s.regValue .rsp) + 48⟩,
      ⟨(Operand.reg 1 : Operand 64), ((s.regValue .rbx).setWidth 32).setWidth 64⟩] }

set_option maxHeartbeats 800000 in
theorem prepareY0_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x104514)
      (codeRange 0x104514 prepareY0Bytes) (Effect.post prepareY0Effect) := by
  advance_begin (lea_r64_effect_step 0x104514 0x49 (by simp [RexWPrefix]) 2 (.base 13 (.d8 32)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x4518 (by decide))
  advance_then (mov_r64_r64_effect_step 0x104518 0x4c 0xf7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x104514 prepareY0Bytes 4 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x451b (by decide))⟩
  advance_then (lea_r64_effect_step 0x10451b 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 48)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x104514 prepareY0Bytes 7 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x4520 (by decide))⟩
  advance_then (mov_r32_r32_effect_step 0x104520 0xd9 rfl)
  case sub => exact codeRange_slice_subset 0x104514 prepareY0Bytes 12 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x4522 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [prepareY0Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareY0Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [prepareY0Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareY0Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]

def prepareY1Bytes : List UInt8 := [0x49,0x8d,0x95,0x80,0x0,0x0,0x0,0x48,0x8d,0xbc,0x24,0x90,0x0,0x0,0x0,0x48,0x8d,0x74,0x24,0x30,0x89,0xd9]

def prepareY1Effect (s : RamState) : Effect :=
  { rip := 0x104589
    writes := [⟨(Operand.reg 2 : Operand 64), (s.regValue .r13) + 128⟩,
      ⟨(Operand.reg 7 : Operand 64), (s.regValue .rsp) + 144⟩,
      ⟨(Operand.reg 6 : Operand 64), (s.regValue .rsp) + 48⟩,
      ⟨(Operand.reg 1 : Operand 64), ((s.regValue .rbx).setWidth 32).setWidth 64⟩] }

set_option maxHeartbeats 800000 in
theorem prepareY1_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x104573)
      (codeRange 0x104573 prepareY1Bytes) (Effect.post prepareY1Effect) := by
  advance_begin (lea_r64_effect_step 0x104573 0x49 (by simp [RexWPrefix]) 2 (.base 13 (.d32 128)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x457a (by decide))
  advance_then (lea_r64_effect_step 0x10457a 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 144)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x104573 prepareY1Bytes 7 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x4582 (by decide))⟩
  advance_then (lea_r64_effect_step 0x104582 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 48)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x104573 prepareY1Bytes 15 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x4587 (by decide))⟩
  advance_then (mov_r32_r32_effect_step 0x104587 0xd9 rfl)
  case sub => exact codeRange_slice_subset 0x104573 prepareY1Bytes 20 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x4589 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [prepareY1Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareY1Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [prepareY1Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareY1Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]

def prepareY2Bytes : List UInt8 := [0x49,0x8d,0x95,0xe0,0x0,0x0,0x0,0x48,0x8d,0xbc,0x24,0x90,0x0,0x0,0x0,0x48,0x8d,0x74,0x24,0x30,0x89,0xd9]

def prepareY2Effect (s : RamState) : Effect :=
  { rip := 0x1045f6
    writes := [⟨(Operand.reg 2 : Operand 64), (s.regValue .r13) + 224⟩,
      ⟨(Operand.reg 7 : Operand 64), (s.regValue .rsp) + 144⟩,
      ⟨(Operand.reg 6 : Operand 64), (s.regValue .rsp) + 48⟩,
      ⟨(Operand.reg 1 : Operand 64), ((s.regValue .rbx).setWidth 32).setWidth 64⟩] }

set_option maxHeartbeats 800000 in
theorem prepareY2_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1045e0)
      (codeRange 0x1045e0 prepareY2Bytes) (Effect.post prepareY2Effect) := by
  advance_begin (lea_r64_effect_step 0x1045e0 0x49 (by simp [RexWPrefix]) 2 (.base 13 (.d32 224)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x45e7 (by decide))
  advance_then (lea_r64_effect_step 0x1045e7 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 144)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1045e0 prepareY2Bytes 7 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x45ef (by decide))⟩
  advance_then (lea_r64_effect_step 0x1045ef 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 48)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1045e0 prepareY2Bytes 15 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x45f4 (by decide))⟩
  advance_then (mov_r32_r32_effect_step 0x1045f4 0xd9 rfl)
  case sub => exact codeRange_slice_subset 0x1045e0 prepareY2Bytes 20 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x45f6 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [prepareY2Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareY2Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [prepareY2Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareY2Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]

def prepareY3Bytes : List UInt8 := [0x49,0x8d,0x95,0x40,0x1,0x0,0x0,0x48,0x8d,0xbc,0x24,0x90,0x0,0x0,0x0,0x48,0x8d,0x74,0x24,0x30,0x89,0xd9]

def prepareY3Effect (s : RamState) : Effect :=
  { rip := 0x10465e
    writes := [⟨(Operand.reg 2 : Operand 64), (s.regValue .r13) + 320⟩,
      ⟨(Operand.reg 7 : Operand 64), (s.regValue .rsp) + 144⟩,
      ⟨(Operand.reg 6 : Operand 64), (s.regValue .rsp) + 48⟩,
      ⟨(Operand.reg 1 : Operand 64), ((s.regValue .rbx).setWidth 32).setWidth 64⟩] }

set_option maxHeartbeats 800000 in
theorem prepareY3_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x104648)
      (codeRange 0x104648 prepareY3Bytes) (Effect.post prepareY3Effect) := by
  advance_begin (lea_r64_effect_step 0x104648 0x49 (by simp [RexWPrefix]) 2 (.base 13 (.d32 320)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x464f (by decide))
  advance_then (lea_r64_effect_step 0x10464f 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 144)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x104648 prepareY3Bytes 7 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x4657 (by decide))⟩
  advance_then (lea_r64_effect_step 0x104657 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 48)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x104648 prepareY3Bytes 15 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x465c (by decide))⟩
  advance_then (mov_r32_r32_effect_step 0x10465c 0xd9 rfl)
  case sub => exact codeRange_slice_subset 0x104648 prepareY3Bytes 20 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x465e (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [prepareY3Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareY3Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [prepareY3Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareY3Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]

def prepareY4Bytes : List UInt8 := [0x49,0x8d,0x95,0xa0,0x1,0x0,0x0,0x48,0x8d,0xbc,0x24,0x90,0x0,0x0,0x0,0x48,0x8d,0x74,0x24,0x30,0x89,0xd9]

def prepareY4Effect (s : RamState) : Effect :=
  { rip := 0x1046c6
    writes := [⟨(Operand.reg 2 : Operand 64), (s.regValue .r13) + 416⟩,
      ⟨(Operand.reg 7 : Operand 64), (s.regValue .rsp) + 144⟩,
      ⟨(Operand.reg 6 : Operand 64), (s.regValue .rsp) + 48⟩,
      ⟨(Operand.reg 1 : Operand 64), ((s.regValue .rbx).setWidth 32).setWidth 64⟩] }

set_option maxHeartbeats 800000 in
theorem prepareY4_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1046b0)
      (codeRange 0x1046b0 prepareY4Bytes) (Effect.post prepareY4Effect) := by
  advance_begin (lea_r64_effect_step 0x1046b0 0x49 (by simp [RexWPrefix]) 2 (.base 13 (.d32 416)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x46b7 (by decide))
  advance_then (lea_r64_effect_step 0x1046b7 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 144)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1046b0 prepareY4Bytes 7 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x46bf (by decide))⟩
  advance_then (lea_r64_effect_step 0x1046bf 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 48)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1046b0 prepareY4Bytes 15 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x46c4 (by decide))⟩
  advance_then (mov_r32_r32_effect_step 0x1046c4 0xd9 rfl)
  case sub => exact codeRange_slice_subset 0x1046b0 prepareY4Bytes 20 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x46c6 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [prepareY4Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareY4Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [prepareY4Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareY4Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]

def prepareY5Bytes : List UInt8 := [0x49,0x8d,0x95,0x0,0x2,0x0,0x0,0x48,0x8d,0xbc,0x24,0x90,0x0,0x0,0x0,0x48,0x8d,0x74,0x24,0x30,0x89,0xd9]

def prepareY5Effect (s : RamState) : Effect :=
  { rip := 0x10472e
    writes := [⟨(Operand.reg 2 : Operand 64), (s.regValue .r13) + 512⟩,
      ⟨(Operand.reg 7 : Operand 64), (s.regValue .rsp) + 144⟩,
      ⟨(Operand.reg 6 : Operand 64), (s.regValue .rsp) + 48⟩,
      ⟨(Operand.reg 1 : Operand 64), ((s.regValue .rbx).setWidth 32).setWidth 64⟩] }

set_option maxHeartbeats 800000 in
theorem prepareY5_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x104718)
      (codeRange 0x104718 prepareY5Bytes) (Effect.post prepareY5Effect) := by
  advance_begin (lea_r64_effect_step 0x104718 0x49 (by simp [RexWPrefix]) 2 (.base 13 (.d32 512)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x471f (by decide))
  advance_then (lea_r64_effect_step 0x10471f 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 144)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x104718 prepareY5Bytes 7 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x4727 (by decide))⟩
  advance_then (lea_r64_effect_step 0x104727 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 48)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x104718 prepareY5Bytes 15 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x472c (by decide))⟩
  advance_then (mov_r32_r32_effect_step 0x10472c 0xd9 rfl)
  case sub => exact codeRange_slice_subset 0x104718 prepareY5Bytes 20 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x472e (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [prepareY5Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareY5Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [prepareY5Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareY5Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]

def prepareY6Bytes : List UInt8 := [0x49,0x8d,0x95,0x60,0x2,0x0,0x0,0x48,0x8d,0xbc,0x24,0x90,0x0,0x0,0x0,0x48,0x8d,0x74,0x24,0x30,0x89,0xd9]

def prepareY6Effect (s : RamState) : Effect :=
  { rip := 0x104796
    writes := [⟨(Operand.reg 2 : Operand 64), (s.regValue .r13) + 608⟩,
      ⟨(Operand.reg 7 : Operand 64), (s.regValue .rsp) + 144⟩,
      ⟨(Operand.reg 6 : Operand 64), (s.regValue .rsp) + 48⟩,
      ⟨(Operand.reg 1 : Operand 64), ((s.regValue .rbx).setWidth 32).setWidth 64⟩] }

set_option maxHeartbeats 800000 in
theorem prepareY6_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x104780)
      (codeRange 0x104780 prepareY6Bytes) (Effect.post prepareY6Effect) := by
  advance_begin (lea_r64_effect_step 0x104780 0x49 (by simp [RexWPrefix]) 2 (.base 13 (.d32 608)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x4787 (by decide))
  advance_then (lea_r64_effect_step 0x104787 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 144)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x104780 prepareY6Bytes 7 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x478f (by decide))⟩
  advance_then (lea_r64_effect_step 0x10478f 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 48)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x104780 prepareY6Bytes 15 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x4794 (by decide))⟩
  advance_then (mov_r32_r32_effect_step 0x104794 0xd9 rfl)
  case sub => exact codeRange_slice_subset 0x104780 prepareY6Bytes 20 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x4796 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [prepareY6Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareY6Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [prepareY6Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareY6Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]

def prepareY7Bytes : List UInt8 := [0x49,0x8d,0x95,0xc0,0x2,0x0,0x0,0x48,0x8d,0xbc,0x24,0x90,0x0,0x0,0x0,0x48,0x8d,0x74,0x24,0x30,0x89,0xd9]

def prepareY7Effect (s : RamState) : Effect :=
  { rip := 0x1047fe
    writes := [⟨(Operand.reg 2 : Operand 64), (s.regValue .r13) + 704⟩,
      ⟨(Operand.reg 7 : Operand 64), (s.regValue .rsp) + 144⟩,
      ⟨(Operand.reg 6 : Operand 64), (s.regValue .rsp) + 48⟩,
      ⟨(Operand.reg 1 : Operand 64), ((s.regValue .rbx).setWidth 32).setWidth 64⟩] }

set_option maxHeartbeats 800000 in
theorem prepareY7_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1047e8)
      (codeRange 0x1047e8 prepareY7Bytes) (Effect.post prepareY7Effect) := by
  advance_begin (lea_r64_effect_step 0x1047e8 0x49 (by simp [RexWPrefix]) 2 (.base 13 (.d32 704)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x47ef (by decide))
  advance_then (lea_r64_effect_step 0x1047ef 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 144)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1047e8 prepareY7Bytes 7 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x47f7 (by decide))⟩
  advance_then (lea_r64_effect_step 0x1047f7 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 48)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1047e8 prepareY7Bytes 15 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x47fc (by decide))⟩
  advance_then (mov_r32_r32_effect_step 0x1047fc 0xd9 rfl)
  case sub => exact codeRange_slice_subset 0x1047e8 prepareY7Bytes 20 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x47fe (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [prepareY7Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareY7Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [prepareY7Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareY7Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]

end P256.Proofs.Projective.Multiply.Machine.Lookup.Scanning
