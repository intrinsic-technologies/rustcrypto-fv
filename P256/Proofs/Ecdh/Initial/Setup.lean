import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.Instructions.MovzxByte
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Not.Generated.R.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Movs.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple
import P256.Proofs.Program.Code

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions.MovzxByte (movzx_r32_r8_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Ecdh.Initial

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def firstBytes : List UInt8 := [15, 182, 232, 76, 141, 188, 36, 248, 6, 0, 0, 72, 141, 180, 36, 248, 0, 0, 0, 76, 137, 255, 76, 137, 234, 137, 233]

def firstEffect (s : RamState) : Effect :=
  { rip := 0x100101
    writes := [⟨(.reg 5 : Operand 64), ((s.regValue .rax).setWidth 8).setWidth 64⟩,
      ⟨(.reg 15 : Operand 64), s.regValue .rsp + 1784⟩,
      ⟨(.reg 6 : Operand 64), s.regValue .rsp + 248⟩,
      ⟨(.reg 7 : Operand 64), s.regValue .rsp + 1784⟩,
      ⟨(.reg 2 : Operand 64), s.regValue .r13⟩,
      ⟨(.reg 1 : Operand 64), ((((s.regValue .rax).setWidth 8).setWidth 64).setWidth 32).setWidth 64⟩] }

set_option maxHeartbeats 800000 in
theorem first_setup [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1000e6)
      (codeRange 0x1000e6 firstBytes) (Effect.post firstEffect) := by
  advance_begin (movzx_r32_r8_effect_step 0x1000e6 0xe8 rfl (by decide))
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0xe9 (by decide))
  advance_then (lea_r64_effect_step 0x1000e9 0x4c (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 1784)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1000e6 firstBytes 3 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xf1 (by decide))⟩
  advance_then (lea_r64_effect_step 0x1000f1 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 248)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1000e6 firstBytes 11 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xf9 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x1000f9 0x4c 0xff (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1000e6 firstBytes 19 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xfc (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x1000fc 0x4c 0xea (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1000e6 firstBytes 22 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xff (by decide))⟩
  advance_then (mov_r32_r32_effect_step 0x1000ff 0xe9 rfl)
  case sub => exact codeRange_slice_subset 0x1000e6 firstBytes 25 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x101 (by decide))⟩
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

def secondBytes : List UInt8 := [72, 141, 148, 36, 24, 4, 0, 0, 72, 141, 188, 36, 24, 7, 0, 0, 76, 137, 246, 137, 233]

def secondEffect (s : RamState) : Effect :=
  { rip := 0x10011b
    writes := [⟨(.reg 2 : Operand 64), s.regValue .rsp + 1048⟩,
      ⟨(.reg 7 : Operand 64), s.regValue .rsp + 1816⟩,
      ⟨(.reg 6 : Operand 64), s.regValue .r14⟩,
      ⟨(.reg 1 : Operand 64), ((s.regValue .rbp).setWidth 32).setWidth 64⟩] }

set_option maxHeartbeats 800000 in
theorem second_setup [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x100106)
      (codeRange 0x100106 secondBytes) (Effect.post secondEffect) := by
  advance_begin (lea_r64_effect_step 0x100106 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 1048)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x10e (by decide))
  advance_then (lea_r64_effect_step 0x10010e 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 1816)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100106 secondBytes 8 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x116 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x100116 0x4c 0xf6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x100106 secondBytes 16 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x119 (by decide))⟩
  advance_then (mov_r32_r32_effect_step 0x100119 0xe9 rfl)
  case sub => exact codeRange_slice_subset 0x100106 secondBytes 19 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x11b (by decide))⟩
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

def thirdBytes : List UInt8 := [72, 141, 148, 36, 56, 4, 0, 0, 72, 141, 188, 36, 56, 7, 0, 0, 76, 137, 230, 137, 233]

def thirdEffect (s : RamState) : Effect :=
  { rip := 0x100135
    writes := [⟨(.reg 2 : Operand 64), s.regValue .rsp + 1080⟩,
      ⟨(.reg 7 : Operand 64), s.regValue .rsp + 1848⟩,
      ⟨(.reg 6 : Operand 64), s.regValue .r12⟩,
      ⟨(.reg 1 : Operand 64), ((s.regValue .rbp).setWidth 32).setWidth 64⟩] }

set_option maxHeartbeats 800000 in
theorem third_setup [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x100120)
      (codeRange 0x100120 thirdBytes) (Effect.post thirdEffect) := by
  advance_begin (lea_r64_effect_step 0x100120 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 1080)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x128 (by decide))
  advance_then (lea_r64_effect_step 0x100128 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 1848)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100120 thirdBytes 8 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x130 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x100130 0x4c 0xe6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x100120 thirdBytes 16 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x133 (by decide))⟩
  advance_then (mov_r32_r32_effect_step 0x100133 0xe9 rfl)
  case sub => exact codeRange_slice_subset 0x100120 thirdBytes 19 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x135 (by decide))⟩
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

end P256.Proofs.Ecdh.Initial
