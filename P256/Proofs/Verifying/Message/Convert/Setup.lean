import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.Instructions.MovzxByte
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions.MovzxByte (movzx_r32_r8_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Verifying.Message.Convert

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def firstBytes : List UInt8 := [0xf, 0xb6, 0xe8, 0x48, 0x8d, 0xbc, 0x24, 0xe8, 0x3, 0x0, 0x0, 0x48, 0x89, 0xe6, 0x4c, 0x89, 0xfa, 0x89, 0xe9]

def firstEffect (s : RamState) : Effect :=
  { rip := 0x10da14
    writes := [⟨(.reg 5 : Operand 64), ((s.regValue .rax).setWidth 8).setWidth 64⟩,
      ⟨(.reg 7 : Operand 64), s.regValue .rsp + 1000⟩,
      ⟨(.reg 6 : Operand 64), s.regValue .rsp⟩,
      ⟨(.reg 2 : Operand 64), s.regValue .r15⟩,
      ⟨(.reg 1 : Operand 64), ((((s.regValue .rax).setWidth 8).setWidth 64).setWidth 32).setWidth 64⟩] }

set_option maxHeartbeats 800000 in
theorem first_setup [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10da01)
      (codeRange 0x10da01 firstBytes) (Effect.post firstEffect) := by
  advance_begin (movzx_r32_r8_effect_step 0x10da01 0xe8 rfl (by decide))
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0xda04 (by decide))
  advance_then (lea_r64_effect_step 0x10da04 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 1000)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10da01 firstBytes 3 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xda0c (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10da0c 0x48 0xe6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10da01 firstBytes 11 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xda0f (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10da0f 0x4c 0xfa (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10da01 firstBytes 14 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xda12 (by decide))⟩
  advance_then (mov_r32_r32_effect_step 0x10da12 0xe9 rfl)
  case sub => exact codeRange_slice_subset 0x10da01 firstBytes 17 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xda14 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [firstEffect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [firstEffect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [firstEffect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [firstEffect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]

def secondBytes : List UInt8 := [0x48, 0x8d, 0x94, 0x24, 0xa0, 0x0, 0x0, 0x0, 0x48, 0x8d, 0xbc, 0x24, 0x8, 0x4, 0x0, 0x0, 0x48, 0x89, 0xde, 0x89, 0xe9]

def secondEffect (s : RamState) : Effect :=
  { rip := 0x10da2e
    writes := [⟨(.reg 2 : Operand 64), s.regValue .rsp + 160⟩,
      ⟨(.reg 7 : Operand 64), s.regValue .rsp + 1032⟩,
      ⟨(.reg 6 : Operand 64), s.regValue .rbx⟩,
      ⟨(.reg 1 : Operand 64), ((s.regValue .rbp).setWidth 32).setWidth 64⟩] }

set_option maxHeartbeats 800000 in
theorem second_setup [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10da19)
      (codeRange 0x10da19 secondBytes) (Effect.post secondEffect) := by
  advance_begin (lea_r64_effect_step 0x10da19 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 160)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0xda21 (by decide))
  advance_then (lea_r64_effect_step 0x10da21 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 1032)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10da19 secondBytes 8 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xda29 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10da29 0x48 0xde (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10da19 secondBytes 16 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xda2c (by decide))⟩
  advance_then (mov_r32_r32_effect_step 0x10da2c 0xe9 rfl)
  case sub => exact codeRange_slice_subset 0x10da19 secondBytes 19 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xda2e (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [secondEffect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [secondEffect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [secondEffect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [secondEffect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]

def thirdBytes : List UInt8 := [0x48, 0x8d, 0x94, 0x24, 0xc0, 0x0, 0x0, 0x0, 0x48, 0x8d, 0xbc, 0x24, 0x28, 0x4, 0x0, 0x0, 0x4c, 0x89, 0xf6, 0x89, 0xe9]

def thirdEffect (s : RamState) : Effect :=
  { rip := 0x10da48
    writes := [⟨(.reg 2 : Operand 64), s.regValue .rsp + 192⟩,
      ⟨(.reg 7 : Operand 64), s.regValue .rsp + 1064⟩,
      ⟨(.reg 6 : Operand 64), s.regValue .r14⟩,
      ⟨(.reg 1 : Operand 64), ((s.regValue .rbp).setWidth 32).setWidth 64⟩] }

set_option maxHeartbeats 800000 in
theorem third_setup [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10da33)
      (codeRange 0x10da33 thirdBytes) (Effect.post thirdEffect) := by
  advance_begin (lea_r64_effect_step 0x10da33 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 192)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0xda3b (by decide))
  advance_then (lea_r64_effect_step 0x10da3b 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 1064)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10da33 thirdBytes 8 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xda43 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10da43 0x4c 0xf6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10da33 thirdBytes 16 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xda46 (by decide))⟩
  advance_then (mov_r32_r32_effect_step 0x10da46 0xe9 rfl)
  case sub => exact codeRange_slice_subset 0x10da33 thirdBytes 19 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xda48 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [thirdEffect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [thirdEffect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [thirdEffect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [thirdEffect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]

end P256.Proofs.Verifying.Message.Convert
