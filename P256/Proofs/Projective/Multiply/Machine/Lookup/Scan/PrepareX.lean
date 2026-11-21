import P256.Proofs.Projective.Multiply.Machine.Lookup.Interface
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.Instructions.MovzxByte
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Add.Generated.Imm32.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions.MovzxByte (movzxR32R8Effect movzx_r32_r8_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Projective.Multiply.Machine.Lookup.Scanning

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

@[local simp] theorem movzx_components (p : BitVec 64) (len : Nat) (dst src : BitVec 5) (s : RamState) :
    (movzxR32R8Effect p len dst src s).components = [.reg dst, .rip] := rfl

def prepareX0Bytes : List UInt8 := [0xf,0xb6,0xd8,0x4c,0x8d,0x64,0x24,0x70,0x4c,0x89,0xe7,0x48,0x89,0xee,0x4c,0x89,0xea,0x89,0xd9]

def prepareX0Effect (s : RamState) : Effect :=
  { rip := 0x10450f
    writes := [⟨(Operand.reg 3 : Operand 64), ((s.regValue .rax).setWidth 8).setWidth 64⟩,
      ⟨(Operand.reg 12 : Operand 64), (s.regValue .rsp) + 112⟩,
      ⟨(Operand.reg 7 : Operand 64), (s.regValue .rsp) + 112⟩,
      ⟨(Operand.reg 6 : Operand 64), s.regValue .rbp⟩,
      ⟨(Operand.reg 2 : Operand 64), s.regValue .r13⟩,
      ⟨(Operand.reg 1 : Operand 64), ((((s.regValue .rax).setWidth 8).setWidth 64).setWidth 32).setWidth 64⟩] }

set_option maxHeartbeats 800000 in
theorem prepareX0_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1044fc)
      (codeRange 0x1044fc prepareX0Bytes) (Effect.post prepareX0Effect) := by
  advance_begin (movzx_r32_r8_effect_step 0x1044fc 0xd8 rfl (by decide))
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x44ff (by decide))
  advance_then (lea_r64_effect_step 0x1044ff 0x4c (by simp [RexWPrefix]) 4 (.sib 4 none 0 (.d8 112)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1044fc prepareX0Bytes 3 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x4504 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x104504 0x4c 0xe7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1044fc prepareX0Bytes 8 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x4507 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x104507 0x48 0xee (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1044fc prepareX0Bytes 11 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x450a (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10450a 0x4c 0xea (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1044fc prepareX0Bytes 14 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x450d (by decide))⟩
  advance_then (mov_r32_r32_effect_step 0x10450d 0xd9 rfl)
  case sub => exact codeRange_slice_subset 0x1044fc prepareX0Bytes 17 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x450f (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [prepareX0Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareX0Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [prepareX0Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareX0Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]

def prepareX1Bytes : List UInt8 := [0x49,0x8d,0x55,0x60,0xf,0xb6,0xd8,0x4c,0x89,0xe7,0x48,0x89,0xee,0x89,0xd9]

def prepareX1Effect (s : RamState) : Effect :=
  { rip := 0x10456e
    writes := [⟨(Operand.reg 2 : Operand 64), (s.regValue .r13) + 96⟩,
      ⟨(Operand.reg 3 : Operand 64), ((s.regValue .rax).setWidth 8).setWidth 64⟩,
      ⟨(Operand.reg 7 : Operand 64), s.regValue .r12⟩,
      ⟨(Operand.reg 6 : Operand 64), s.regValue .rbp⟩,
      ⟨(Operand.reg 1 : Operand 64), ((((s.regValue .rax).setWidth 8).setWidth 64).setWidth 32).setWidth 64⟩] }

set_option maxHeartbeats 800000 in
theorem prepareX1_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10455f)
      (codeRange 0x10455f prepareX1Bytes) (Effect.post prepareX1Effect) := by
  advance_begin (lea_r64_effect_step 0x10455f 0x49 (by simp [RexWPrefix]) 2 (.base 13 (.d8 96)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x4563 (by decide))
  advance_then (movzx_r32_r8_effect_step 0x104563 0xd8 rfl (by decide))
  case sub => exact codeRange_slice_subset 0x10455f prepareX1Bytes 4 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x4566 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x104566 0x4c 0xe7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10455f prepareX1Bytes 7 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x4569 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x104569 0x48 0xee (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10455f prepareX1Bytes 10 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x456c (by decide))⟩
  advance_then (mov_r32_r32_effect_step 0x10456c 0xd9 rfl)
  case sub => exact codeRange_slice_subset 0x10455f prepareX1Bytes 13 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x456e (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [prepareX1Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareX1Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [prepareX1Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareX1Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]

def prepareX2Bytes : List UInt8 := [0x49,0x8d,0x95,0xc0,0x0,0x0,0x0,0xf,0xb6,0xd8,0x4c,0x89,0xe7,0x4c,0x89,0xf6,0x89,0xd9]

def prepareX2Effect (s : RamState) : Effect :=
  { rip := 0x1045db
    writes := [⟨(Operand.reg 2 : Operand 64), (s.regValue .r13) + 192⟩,
      ⟨(Operand.reg 3 : Operand 64), ((s.regValue .rax).setWidth 8).setWidth 64⟩,
      ⟨(Operand.reg 7 : Operand 64), s.regValue .r12⟩,
      ⟨(Operand.reg 6 : Operand 64), s.regValue .r14⟩,
      ⟨(Operand.reg 1 : Operand 64), ((((s.regValue .rax).setWidth 8).setWidth 64).setWidth 32).setWidth 64⟩] }

set_option maxHeartbeats 800000 in
theorem prepareX2_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1045c9)
      (codeRange 0x1045c9 prepareX2Bytes) (Effect.post prepareX2Effect) := by
  advance_begin (lea_r64_effect_step 0x1045c9 0x49 (by simp [RexWPrefix]) 2 (.base 13 (.d32 192)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x45d0 (by decide))
  advance_then (movzx_r32_r8_effect_step 0x1045d0 0xd8 rfl (by decide))
  case sub => exact codeRange_slice_subset 0x1045c9 prepareX2Bytes 7 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x45d3 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x1045d3 0x4c 0xe7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1045c9 prepareX2Bytes 10 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x45d6 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x1045d6 0x4c 0xf6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1045c9 prepareX2Bytes 13 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x45d9 (by decide))⟩
  advance_then (mov_r32_r32_effect_step 0x1045d9 0xd9 rfl)
  case sub => exact codeRange_slice_subset 0x1045c9 prepareX2Bytes 16 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x45db (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [prepareX2Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareX2Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [prepareX2Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareX2Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]

def prepareX3Bytes : List UInt8 := [0x49,0x8d,0x95,0x20,0x1,0x0,0x0,0xf,0xb6,0xd8,0x4c,0x89,0xe7,0x4c,0x89,0xf6,0x89,0xd9]

def prepareX3Effect (s : RamState) : Effect :=
  { rip := 0x104643
    writes := [⟨(Operand.reg 2 : Operand 64), (s.regValue .r13) + 288⟩,
      ⟨(Operand.reg 3 : Operand 64), ((s.regValue .rax).setWidth 8).setWidth 64⟩,
      ⟨(Operand.reg 7 : Operand 64), s.regValue .r12⟩,
      ⟨(Operand.reg 6 : Operand 64), s.regValue .r14⟩,
      ⟨(Operand.reg 1 : Operand 64), ((((s.regValue .rax).setWidth 8).setWidth 64).setWidth 32).setWidth 64⟩] }

set_option maxHeartbeats 800000 in
theorem prepareX3_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x104631)
      (codeRange 0x104631 prepareX3Bytes) (Effect.post prepareX3Effect) := by
  advance_begin (lea_r64_effect_step 0x104631 0x49 (by simp [RexWPrefix]) 2 (.base 13 (.d32 288)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x4638 (by decide))
  advance_then (movzx_r32_r8_effect_step 0x104638 0xd8 rfl (by decide))
  case sub => exact codeRange_slice_subset 0x104631 prepareX3Bytes 7 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x463b (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10463b 0x4c 0xe7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x104631 prepareX3Bytes 10 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x463e (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10463e 0x4c 0xf6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x104631 prepareX3Bytes 13 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x4641 (by decide))⟩
  advance_then (mov_r32_r32_effect_step 0x104641 0xd9 rfl)
  case sub => exact codeRange_slice_subset 0x104631 prepareX3Bytes 16 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x4643 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [prepareX3Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareX3Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [prepareX3Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareX3Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]

def prepareX4Bytes : List UInt8 := [0x49,0x8d,0x95,0x80,0x1,0x0,0x0,0xf,0xb6,0xd8,0x4c,0x89,0xe7,0x4c,0x89,0xf6,0x89,0xd9]

def prepareX4Effect (s : RamState) : Effect :=
  { rip := 0x1046ab
    writes := [⟨(Operand.reg 2 : Operand 64), (s.regValue .r13) + 384⟩,
      ⟨(Operand.reg 3 : Operand 64), ((s.regValue .rax).setWidth 8).setWidth 64⟩,
      ⟨(Operand.reg 7 : Operand 64), s.regValue .r12⟩,
      ⟨(Operand.reg 6 : Operand 64), s.regValue .r14⟩,
      ⟨(Operand.reg 1 : Operand 64), ((((s.regValue .rax).setWidth 8).setWidth 64).setWidth 32).setWidth 64⟩] }

set_option maxHeartbeats 800000 in
theorem prepareX4_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x104699)
      (codeRange 0x104699 prepareX4Bytes) (Effect.post prepareX4Effect) := by
  advance_begin (lea_r64_effect_step 0x104699 0x49 (by simp [RexWPrefix]) 2 (.base 13 (.d32 384)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x46a0 (by decide))
  advance_then (movzx_r32_r8_effect_step 0x1046a0 0xd8 rfl (by decide))
  case sub => exact codeRange_slice_subset 0x104699 prepareX4Bytes 7 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x46a3 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x1046a3 0x4c 0xe7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x104699 prepareX4Bytes 10 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x46a6 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x1046a6 0x4c 0xf6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x104699 prepareX4Bytes 13 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x46a9 (by decide))⟩
  advance_then (mov_r32_r32_effect_step 0x1046a9 0xd9 rfl)
  case sub => exact codeRange_slice_subset 0x104699 prepareX4Bytes 16 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x46ab (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [prepareX4Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareX4Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [prepareX4Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareX4Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]

def prepareX5Bytes : List UInt8 := [0x49,0x8d,0x95,0xe0,0x1,0x0,0x0,0xf,0xb6,0xd8,0x4c,0x89,0xe7,0x4c,0x89,0xf6,0x89,0xd9]

def prepareX5Effect (s : RamState) : Effect :=
  { rip := 0x104713
    writes := [⟨(Operand.reg 2 : Operand 64), (s.regValue .r13) + 480⟩,
      ⟨(Operand.reg 3 : Operand 64), ((s.regValue .rax).setWidth 8).setWidth 64⟩,
      ⟨(Operand.reg 7 : Operand 64), s.regValue .r12⟩,
      ⟨(Operand.reg 6 : Operand 64), s.regValue .r14⟩,
      ⟨(Operand.reg 1 : Operand 64), ((((s.regValue .rax).setWidth 8).setWidth 64).setWidth 32).setWidth 64⟩] }

set_option maxHeartbeats 800000 in
theorem prepareX5_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x104701)
      (codeRange 0x104701 prepareX5Bytes) (Effect.post prepareX5Effect) := by
  advance_begin (lea_r64_effect_step 0x104701 0x49 (by simp [RexWPrefix]) 2 (.base 13 (.d32 480)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x4708 (by decide))
  advance_then (movzx_r32_r8_effect_step 0x104708 0xd8 rfl (by decide))
  case sub => exact codeRange_slice_subset 0x104701 prepareX5Bytes 7 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x470b (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10470b 0x4c 0xe7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x104701 prepareX5Bytes 10 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x470e (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10470e 0x4c 0xf6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x104701 prepareX5Bytes 13 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x4711 (by decide))⟩
  advance_then (mov_r32_r32_effect_step 0x104711 0xd9 rfl)
  case sub => exact codeRange_slice_subset 0x104701 prepareX5Bytes 16 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x4713 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [prepareX5Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareX5Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [prepareX5Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareX5Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]

def prepareX6Bytes : List UInt8 := [0x49,0x8d,0x95,0x40,0x2,0x0,0x0,0xf,0xb6,0xd8,0x4c,0x89,0xe7,0x4c,0x89,0xf6,0x89,0xd9]

def prepareX6Effect (s : RamState) : Effect :=
  { rip := 0x10477b
    writes := [⟨(Operand.reg 2 : Operand 64), (s.regValue .r13) + 576⟩,
      ⟨(Operand.reg 3 : Operand 64), ((s.regValue .rax).setWidth 8).setWidth 64⟩,
      ⟨(Operand.reg 7 : Operand 64), s.regValue .r12⟩,
      ⟨(Operand.reg 6 : Operand 64), s.regValue .r14⟩,
      ⟨(Operand.reg 1 : Operand 64), ((((s.regValue .rax).setWidth 8).setWidth 64).setWidth 32).setWidth 64⟩] }

set_option maxHeartbeats 800000 in
theorem prepareX6_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x104769)
      (codeRange 0x104769 prepareX6Bytes) (Effect.post prepareX6Effect) := by
  advance_begin (lea_r64_effect_step 0x104769 0x49 (by simp [RexWPrefix]) 2 (.base 13 (.d32 576)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x4770 (by decide))
  advance_then (movzx_r32_r8_effect_step 0x104770 0xd8 rfl (by decide))
  case sub => exact codeRange_slice_subset 0x104769 prepareX6Bytes 7 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x4773 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x104773 0x4c 0xe7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x104769 prepareX6Bytes 10 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x4776 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x104776 0x4c 0xf6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x104769 prepareX6Bytes 13 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x4779 (by decide))⟩
  advance_then (mov_r32_r32_effect_step 0x104779 0xd9 rfl)
  case sub => exact codeRange_slice_subset 0x104769 prepareX6Bytes 16 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x477b (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [prepareX6Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareX6Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [prepareX6Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareX6Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]

def prepareX7Bytes : List UInt8 := [0x49,0x8d,0x95,0xa0,0x2,0x0,0x0,0xf,0xb6,0xd8,0x4c,0x89,0xe7,0x4c,0x89,0xf6,0x89,0xd9]

def prepareX7Effect (s : RamState) : Effect :=
  { rip := 0x1047e3
    writes := [⟨(Operand.reg 2 : Operand 64), (s.regValue .r13) + 672⟩,
      ⟨(Operand.reg 3 : Operand 64), ((s.regValue .rax).setWidth 8).setWidth 64⟩,
      ⟨(Operand.reg 7 : Operand 64), s.regValue .r12⟩,
      ⟨(Operand.reg 6 : Operand 64), s.regValue .r14⟩,
      ⟨(Operand.reg 1 : Operand 64), ((((s.regValue .rax).setWidth 8).setWidth 64).setWidth 32).setWidth 64⟩] }

set_option maxHeartbeats 800000 in
theorem prepareX7_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1047d1)
      (codeRange 0x1047d1 prepareX7Bytes) (Effect.post prepareX7Effect) := by
  advance_begin (lea_r64_effect_step 0x1047d1 0x49 (by simp [RexWPrefix]) 2 (.base 13 (.d32 672)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x47d8 (by decide))
  advance_then (movzx_r32_r8_effect_step 0x1047d8 0xd8 rfl (by decide))
  case sub => exact codeRange_slice_subset 0x1047d1 prepareX7Bytes 7 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x47db (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x1047db 0x4c 0xe7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1047d1 prepareX7Bytes 10 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x47de (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x1047de 0x4c 0xf6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1047d1 prepareX7Bytes 13 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x47e1 (by decide))⟩
  advance_then (mov_r32_r32_effect_step 0x1047e1 0xd9 rfl)
  case sub => exact codeRange_slice_subset 0x1047d1 prepareX7Bytes 16 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x47e3 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [prepareX7Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareX7Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [prepareX7Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareX7Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]

end P256.Proofs.Projective.Multiply.Machine.Lookup.Scanning
