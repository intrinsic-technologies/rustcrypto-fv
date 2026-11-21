import P256.Proofs.Projective.Multiply.Machine.Lookup.Interface
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.Instructions.MovzxByte
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Add.Generated.Imm32.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions.MovzxByte (movzx_r32_r8_rex_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Projective.Multiply.Machine.Lookup.Finishing

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def prepareSelectX0Bytes : List UInt8 := [0x40,0xf,0xb6,0xed,0x4c,0x8d,0x64,0x24,0x70,0x48,0x8d,0x94,0x24,0xd8,0x0,0x0,0x0,0x4c,0x89,0xe7,0x4c,0x89,0xf6,0x89,0xe9]

def prepareSelectX0Effect (s : RamState) : Effect :=
  { rip := 0x10490a
    writes := [⟨(Operand.reg 5 : Operand 64), ((s.regValue .rbp).setWidth 8).setWidth 64⟩,
      ⟨(Operand.reg 12 : Operand 64), (s.regValue .rsp) + 112⟩,
      ⟨(Operand.reg 2 : Operand 64), (s.regValue .rsp) + 216⟩,
      ⟨(Operand.reg 7 : Operand 64), (s.regValue .rsp) + 112⟩,
      ⟨(Operand.reg 6 : Operand 64), s.regValue .r14⟩,
      ⟨(Operand.reg 1 : Operand 64), ((((s.regValue .rbp).setWidth 8).setWidth 64).setWidth 32).setWidth 64⟩] }

set_option maxHeartbeats 800000 in
theorem prepareSelectX0_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1048f1)
      (codeRange 0x1048f1 prepareSelectX0Bytes) (Effect.post prepareSelectX0Effect) := by
  advance_begin (movzx_r32_r8_rex_effect_step 0x1048f1 0x40 0xed (by simp [RexNoWPrefix]) rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x48f5 (by decide))
  advance_then (lea_r64_effect_step 0x1048f5 0x4c (by simp [RexWPrefix]) 4 (.sib 4 none 0 (.d8 112)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1048f1 prepareSelectX0Bytes 4 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x48fa (by decide))⟩
  advance_then (lea_r64_effect_step 0x1048fa 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 216)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1048f1 prepareSelectX0Bytes 9 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x4902 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x104902 0x4c 0xe7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1048f1 prepareSelectX0Bytes 17 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x4905 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x104905 0x4c 0xf6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1048f1 prepareSelectX0Bytes 20 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x4908 (by decide))⟩
  advance_then (mov_r32_r32_effect_step 0x104908 0xe9 rfl)
  case sub => exact codeRange_slice_subset 0x1048f1 prepareSelectX0Bytes 23 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x490a (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [prepareSelectX0Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareSelectX0Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [prepareSelectX0Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareSelectX0Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]

end P256.Proofs.Projective.Multiply.Machine.Lookup.Finishing
