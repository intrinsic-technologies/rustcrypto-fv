import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program
open P256.Spec.Program.Routines

namespace P256.Proofs.Verifying.Combination.Loop.Multi

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def doubleInputSetupBytes : List UInt8 :=
  [0xb9, 0xc, 0, 0, 0, 0x4c, 0x89, 0xff, 0x4c, 0x8d, 0x64, 0x24, 0x48,
    0x4c, 0x89, 0xe6]

def doubleInputSetupEffect (s : RamState) : Effect :=
  { rip := 0x10f18a
    writes := [⟨(Operand.reg 1 : Operand 64), 12⟩,
      ⟨(Operand.reg 7 : Operand 64), s.regValue .r15⟩,
      ⟨(Operand.reg 12 : Operand 64), stackPtr s + 72⟩,
      ⟨(Operand.reg 6 : Operand 64), stackPtr s + 72⟩] }

theorem doubleInputSetup_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10f17a)
      (codeRange 0x10f17a doubleInputSetupBytes) (Effect.post doubleInputSetupEffect) := by
  advance_begin (mov_r32_imm32_effect_step 0x10f17a 0xb9 (by decide) 12)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0xf17f (by decide))
  advance_then (mov_r64_r64_effect_step 0x10f17f 0x4c 0xff (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10f17a doubleInputSetupBytes 5 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xf182 (by decide))⟩
  advance_then (lea_r64_effect_step 0x10f182 0x4c (by simp [RexWPrefix]) 4
    (.sib 4 none 0 (.d8 72)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f17a doubleInputSetupBytes 8 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xf187 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10f187 0x4c 0xe6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10f17a doubleInputSetupBytes 13 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xf18a (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [doubleInputSetupEffect]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [doubleInputSetupEffect]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [doubleInputSetupEffect]
  · x86_norm [doubleInputSetupEffect]
    all_goals (repeat first | constructor | rfl)

def doubleOutputSetupBytes : List UInt8 :=
  [0xb9, 0xc, 0x0, 0x0, 0x0, 0x4c, 0x89, 0xe7, 0x4c, 0x89, 0xfe]

def doubleOutputSetupEffect (s : RamState) : Effect :=
  { rip := 0x10f1a0
    writes := [⟨(Operand.reg 1 : Operand 64), 12⟩,
      ⟨(Operand.reg 7 : Operand 64), s.regValue .r12⟩,
      ⟨(Operand.reg 6 : Operand 64), s.regValue .r15⟩] }

theorem doubleOutputSetup_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10f195)
      (codeRange 0x10f195 doubleOutputSetupBytes) (Effect.post doubleOutputSetupEffect) := by
  advance_begin (mov_r32_imm32_effect_step 0x10f195 0xb9 (by decide) 12)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0xf19a (by decide))
  advance_then (mov_r64_r64_effect_step 0x10f19a 0x4c 0xe7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10f195 doubleOutputSetupBytes 5 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xf19d (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10f19d 0x4c 0xfe (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10f195 doubleOutputSetupBytes 8 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xf1a0 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [doubleOutputSetupEffect]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [doubleOutputSetupEffect]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [doubleOutputSetupEffect]
  · x86_norm [doubleOutputSetupEffect]
    all_goals (repeat first | constructor | rfl)


end P256.Proofs.Verifying.Combination.Loop.Multi
