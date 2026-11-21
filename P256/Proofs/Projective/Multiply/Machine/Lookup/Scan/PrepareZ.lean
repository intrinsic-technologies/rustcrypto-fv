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

attribute [local x86_compose] addR64Imm32Effect

def prepareZ0Bytes : List UInt8 := [0x49,0x8d,0x55,0x40,0x48,0x8d,0xbc,0x24,0xb0,0x0,0x0,0x0,0x48,0x8d,0x74,0x24,0x50,0x89,0xd9]

def prepareZ0Effect (s : RamState) : Effect :=
  { rip := 0x10453a
    writes := [⟨(Operand.reg 2 : Operand 64), (s.regValue .r13) + 64⟩,
      ⟨(Operand.reg 7 : Operand 64), (s.regValue .rsp) + 176⟩,
      ⟨(Operand.reg 6 : Operand 64), (s.regValue .rsp) + 80⟩,
      ⟨(Operand.reg 1 : Operand 64), ((s.regValue .rbx).setWidth 32).setWidth 64⟩] }

set_option maxHeartbeats 800000 in
theorem prepareZ0_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x104527)
      (codeRange 0x104527 prepareZ0Bytes) (Effect.post prepareZ0Effect) := by
  advance_begin (lea_r64_effect_step 0x104527 0x49 (by simp [RexWPrefix]) 2 (.base 13 (.d8 64)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x452b (by decide))
  advance_then (lea_r64_effect_step 0x10452b 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 176)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x104527 prepareZ0Bytes 4 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x4533 (by decide))⟩
  advance_then (lea_r64_effect_step 0x104533 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 80)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x104527 prepareZ0Bytes 12 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x4538 (by decide))⟩
  advance_then (mov_r32_r32_effect_step 0x104538 0xd9 rfl)
  case sub => exact codeRange_slice_subset 0x104527 prepareZ0Bytes 17 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x453a (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [prepareZ0Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareZ0Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [prepareZ0Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareZ0Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]

def prepareZ1Bytes : List UInt8 := [0x49,0x8d,0x95,0xa0,0x0,0x0,0x0,0x48,0x8d,0xbc,0x24,0xb0,0x0,0x0,0x0,0x48,0x8d,0x74,0x24,0x50,0x48,0x89,0xf5,0x89,0xd9]

def prepareZ1Effect (s : RamState) : Effect :=
  { rip := 0x1045a7
    writes := [⟨(Operand.reg 2 : Operand 64), (s.regValue .r13) + 160⟩,
      ⟨(Operand.reg 7 : Operand 64), (s.regValue .rsp) + 176⟩,
      ⟨(Operand.reg 6 : Operand 64), (s.regValue .rsp) + 80⟩,
      ⟨(Operand.reg 5 : Operand 64), (s.regValue .rsp) + 80⟩,
      ⟨(Operand.reg 1 : Operand 64), ((s.regValue .rbx).setWidth 32).setWidth 64⟩] }

set_option maxHeartbeats 800000 in
theorem prepareZ1_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10458e)
      (codeRange 0x10458e prepareZ1Bytes) (Effect.post prepareZ1Effect) := by
  advance_begin (lea_r64_effect_step 0x10458e 0x49 (by simp [RexWPrefix]) 2 (.base 13 (.d32 160)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x4595 (by decide))
  advance_then (lea_r64_effect_step 0x104595 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 176)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10458e prepareZ1Bytes 7 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x459d (by decide))⟩
  advance_then (lea_r64_effect_step 0x10459d 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 80)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10458e prepareZ1Bytes 15 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x45a2 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x1045a2 0x48 0xf5 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10458e prepareZ1Bytes 20 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x45a5 (by decide))⟩
  advance_then (mov_r32_r32_effect_step 0x1045a5 0xd9 rfl)
  case sub => exact codeRange_slice_subset 0x10458e prepareZ1Bytes 23 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x45a7 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [prepareZ1Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareZ1Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [prepareZ1Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareZ1Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]

def prepareZ2Bytes : List UInt8 := [0x49,0x8d,0x95,0x0,0x1,0x0,0x0,0x48,0x8d,0xbc,0x24,0xb0,0x0,0x0,0x0,0x48,0x89,0xee,0x89,0xd9]

def prepareZ2Effect (s : RamState) : Effect :=
  { rip := 0x10460f
    writes := [⟨(Operand.reg 2 : Operand 64), (s.regValue .r13) + 256⟩,
      ⟨(Operand.reg 7 : Operand 64), (s.regValue .rsp) + 176⟩,
      ⟨(Operand.reg 6 : Operand 64), s.regValue .rbp⟩,
      ⟨(Operand.reg 1 : Operand 64), ((s.regValue .rbx).setWidth 32).setWidth 64⟩] }

set_option maxHeartbeats 800000 in
theorem prepareZ2_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1045fb)
      (codeRange 0x1045fb prepareZ2Bytes) (Effect.post prepareZ2Effect) := by
  advance_begin (lea_r64_effect_step 0x1045fb 0x49 (by simp [RexWPrefix]) 2 (.base 13 (.d32 256)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x4602 (by decide))
  advance_then (lea_r64_effect_step 0x104602 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 176)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1045fb prepareZ2Bytes 7 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x460a (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10460a 0x48 0xee (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1045fb prepareZ2Bytes 15 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x460d (by decide))⟩
  advance_then (mov_r32_r32_effect_step 0x10460d 0xd9 rfl)
  case sub => exact codeRange_slice_subset 0x1045fb prepareZ2Bytes 18 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x460f (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [prepareZ2Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareZ2Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [prepareZ2Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareZ2Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]

def prepareZ3Bytes : List UInt8 := [0x49,0x8d,0x95,0x60,0x1,0x0,0x0,0x48,0x8d,0xbc,0x24,0xb0,0x0,0x0,0x0,0x48,0x89,0xee,0x89,0xd9]

def prepareZ3Effect (s : RamState) : Effect :=
  { rip := 0x104677
    writes := [⟨(Operand.reg 2 : Operand 64), (s.regValue .r13) + 352⟩,
      ⟨(Operand.reg 7 : Operand 64), (s.regValue .rsp) + 176⟩,
      ⟨(Operand.reg 6 : Operand 64), s.regValue .rbp⟩,
      ⟨(Operand.reg 1 : Operand 64), ((s.regValue .rbx).setWidth 32).setWidth 64⟩] }

set_option maxHeartbeats 800000 in
theorem prepareZ3_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x104663)
      (codeRange 0x104663 prepareZ3Bytes) (Effect.post prepareZ3Effect) := by
  advance_begin (lea_r64_effect_step 0x104663 0x49 (by simp [RexWPrefix]) 2 (.base 13 (.d32 352)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x466a (by decide))
  advance_then (lea_r64_effect_step 0x10466a 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 176)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x104663 prepareZ3Bytes 7 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x4672 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x104672 0x48 0xee (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x104663 prepareZ3Bytes 15 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x4675 (by decide))⟩
  advance_then (mov_r32_r32_effect_step 0x104675 0xd9 rfl)
  case sub => exact codeRange_slice_subset 0x104663 prepareZ3Bytes 18 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x4677 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [prepareZ3Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareZ3Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [prepareZ3Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareZ3Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]

def prepareZ4Bytes : List UInt8 := [0x49,0x8d,0x95,0xc0,0x1,0x0,0x0,0x48,0x8d,0xbc,0x24,0xb0,0x0,0x0,0x0,0x48,0x89,0xee,0x89,0xd9]

def prepareZ4Effect (s : RamState) : Effect :=
  { rip := 0x1046df
    writes := [⟨(Operand.reg 2 : Operand 64), (s.regValue .r13) + 448⟩,
      ⟨(Operand.reg 7 : Operand 64), (s.regValue .rsp) + 176⟩,
      ⟨(Operand.reg 6 : Operand 64), s.regValue .rbp⟩,
      ⟨(Operand.reg 1 : Operand 64), ((s.regValue .rbx).setWidth 32).setWidth 64⟩] }

set_option maxHeartbeats 800000 in
theorem prepareZ4_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1046cb)
      (codeRange 0x1046cb prepareZ4Bytes) (Effect.post prepareZ4Effect) := by
  advance_begin (lea_r64_effect_step 0x1046cb 0x49 (by simp [RexWPrefix]) 2 (.base 13 (.d32 448)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x46d2 (by decide))
  advance_then (lea_r64_effect_step 0x1046d2 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 176)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1046cb prepareZ4Bytes 7 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x46da (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x1046da 0x48 0xee (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1046cb prepareZ4Bytes 15 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x46dd (by decide))⟩
  advance_then (mov_r32_r32_effect_step 0x1046dd 0xd9 rfl)
  case sub => exact codeRange_slice_subset 0x1046cb prepareZ4Bytes 18 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x46df (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [prepareZ4Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareZ4Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [prepareZ4Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareZ4Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]

def prepareZ5Bytes : List UInt8 := [0x49,0x8d,0x95,0x20,0x2,0x0,0x0,0x48,0x8d,0xbc,0x24,0xb0,0x0,0x0,0x0,0x48,0x89,0xee,0x89,0xd9]

def prepareZ5Effect (s : RamState) : Effect :=
  { rip := 0x104747
    writes := [⟨(Operand.reg 2 : Operand 64), (s.regValue .r13) + 544⟩,
      ⟨(Operand.reg 7 : Operand 64), (s.regValue .rsp) + 176⟩,
      ⟨(Operand.reg 6 : Operand 64), s.regValue .rbp⟩,
      ⟨(Operand.reg 1 : Operand 64), ((s.regValue .rbx).setWidth 32).setWidth 64⟩] }

set_option maxHeartbeats 800000 in
theorem prepareZ5_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x104733)
      (codeRange 0x104733 prepareZ5Bytes) (Effect.post prepareZ5Effect) := by
  advance_begin (lea_r64_effect_step 0x104733 0x49 (by simp [RexWPrefix]) 2 (.base 13 (.d32 544)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x473a (by decide))
  advance_then (lea_r64_effect_step 0x10473a 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 176)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x104733 prepareZ5Bytes 7 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x4742 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x104742 0x48 0xee (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x104733 prepareZ5Bytes 15 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x4745 (by decide))⟩
  advance_then (mov_r32_r32_effect_step 0x104745 0xd9 rfl)
  case sub => exact codeRange_slice_subset 0x104733 prepareZ5Bytes 18 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x4747 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [prepareZ5Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareZ5Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [prepareZ5Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareZ5Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]

def prepareZ6Bytes : List UInt8 := [0x49,0x8d,0x95,0x80,0x2,0x0,0x0,0x48,0x8d,0xbc,0x24,0xb0,0x0,0x0,0x0,0x48,0x89,0xee,0x89,0xd9]

def prepareZ6Effect (s : RamState) : Effect :=
  { rip := 0x1047af
    writes := [⟨(Operand.reg 2 : Operand 64), (s.regValue .r13) + 640⟩,
      ⟨(Operand.reg 7 : Operand 64), (s.regValue .rsp) + 176⟩,
      ⟨(Operand.reg 6 : Operand 64), s.regValue .rbp⟩,
      ⟨(Operand.reg 1 : Operand 64), ((s.regValue .rbx).setWidth 32).setWidth 64⟩] }

set_option maxHeartbeats 800000 in
theorem prepareZ6_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10479b)
      (codeRange 0x10479b prepareZ6Bytes) (Effect.post prepareZ6Effect) := by
  advance_begin (lea_r64_effect_step 0x10479b 0x49 (by simp [RexWPrefix]) 2 (.base 13 (.d32 640)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x47a2 (by decide))
  advance_then (lea_r64_effect_step 0x1047a2 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 176)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10479b prepareZ6Bytes 7 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x47aa (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x1047aa 0x48 0xee (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10479b prepareZ6Bytes 15 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x47ad (by decide))⟩
  advance_then (mov_r32_r32_effect_step 0x1047ad 0xd9 rfl)
  case sub => exact codeRange_slice_subset 0x10479b prepareZ6Bytes 18 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x47af (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [prepareZ6Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareZ6Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [prepareZ6Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareZ6Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]

def prepareZ7Bytes : List UInt8 := [0x49,0x81,0xc5,0xe0,0x2,0x0,0x0,0x48,0x8d,0xbc,0x24,0xb0,0x0,0x0,0x0,0x48,0x89,0xee,0x4c,0x89,0xea,0x89,0xd9]

def prepareZ7Effect (s : RamState) : Effect :=
  { rip := 0x10481a
    writes := [⟨(Operand.reg 13 : Operand 64), (s.regValue .r13) + 736⟩,
      ⟨(Operand.reg 7 : Operand 64), (s.regValue .rsp) + 176⟩,
      ⟨(Operand.reg 6 : Operand 64), s.regValue .rbp⟩,
      ⟨(Operand.reg 2 : Operand 64), (s.regValue .r13) + 736⟩,
      ⟨(Operand.reg 1 : Operand 64), ((s.regValue .rbx).setWidth 32).setWidth 64⟩]
    flags := some (.ofStatusFlags (addSpec (s.regValue .r13) 736).2) }

set_option maxHeartbeats 800000 in
theorem prepareZ7_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x104803)
      (codeRange 0x104803 prepareZ7Bytes) (Effect.post prepareZ7Effect) := by
  advance_begin (add_r64_imm32_effect_step 0x104803 0x49 0xc5 736 (by simp [RexWPrefix]) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x480a (by decide))
  advance_then (lea_r64_effect_step 0x10480a 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 176)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x104803 prepareZ7Bytes 7 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x4812 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x104812 0x48 0xee (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x104803 prepareZ7Bytes 15 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x4815 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x104815 0x4c 0xea (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x104803 prepareZ7Bytes 18 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x4818 (by decide))⟩
  advance_then (mov_r32_r32_effect_step 0x104818 0xd9 rfl)
  case sub => exact codeRange_slice_subset 0x104803 prepareZ7Bytes 21 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x481a (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [prepareZ7Effect, addSpec]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareZ7Effect, addSpec]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [prepareZ7Effect, addSpec]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareZ7Effect, addSpec]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]

end P256.Proofs.Projective.Multiply.Machine.Lookup.Scanning
