import P256.Proofs.Verifying.Combination.Naf.Interface
import P256.Proofs.Verifying.Combination.Naf.Machine.Setup
import X86Proofs.Instructions.And.Generated.Imm8.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)

namespace P256.Proofs.Verifying.Combination.Naf.Machine

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar

attribute [local x86_compose] andR32Imm8Effect

def headerBytes : List UInt8 :=
  [0x4c,0x89,0xfe,0x48,0xc1,0xee,6,0x44,0x89,0xfb,0x83,0xe3,0x3f,
   0x48,0x8d,0x7c,0x24,0x30]

def headerEffect (s : RamState) : Effect :=
  { rip := 0x10f3f9
    writes := [⟨(Operand.reg 6 : Operand 64), (Operand.reg 15 : Operand 64).read s >>> 6⟩,
      ⟨(Operand.reg 3 : Operand 64), ((Operand.reg 15 : Operand 32).read s &&& 63).setWidth 64⟩,
      ⟨(Operand.reg 7 : Operand 64), rspOf s+48⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

theorem header_block [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10f3e7) (codeRange 0x10f3e7 headerBytes)
      (Effect.post headerEffect) := by
  have next (offset : Nat) (bound : offset < 118431) :=
    boundary_ne_program hout (inProgram_of_textOffset offset bound)
  advance_begin (show StepEffect _ _ (movR64R64Effect 0x10f3e7 6 15) from
    mov_r64_r64_effect_step 0x10f3e7 0x4c 0xfe (by simp [RexWPrefix]) rfl)
  case next => intro _ _; exact next 0xf3ea (by decide)
  advance_then (show StepEffect _ _ (shrR64Effect 0x10f3ea 4 6 6) from
    shr_r64_imm8_effect_step 0x10f3ea 0x48 0xee 6 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f3e7 headerBytes 3 4
  case mid =>
    intro s t hp he ho
    exact ⟨he.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, next 0xf3ee (by decide)⟩
  advance_then (show StepEffect _ _ (movR32R32Effect 0x10f3ee 3 3 15) from
    mov_r32_r32_rex_effect_step 0x10f3ee 0x44 0xfb (by simp [RexNoWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10f3e7 headerBytes 7 3
  case mid =>
    intro s t hp he ho
    exact ⟨he.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, next 0xf3f1 (by decide)⟩
  advance_then (show StepEffect _ _ (andR32Imm8Effect 0x10f3f1 3 3 63) from
    and_r32_imm8_effect_step 0x10f3f1 0xe3 63 rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f3e7 headerBytes 10 3
  case mid =>
    intro s t hp he ho
    exact ⟨he.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, next 0xf3f4 (by decide)⟩
  advance_then (lea_r64_effect_step 0x10f3f4 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d8 48)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f3e7 headerBytes 13 5
  case mid =>
    intro s t hp he ho
    exact ⟨he.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, next 0xf3f9 (by decide)⟩
  have narrow (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := by
    rw [BitVec.setWidth_setWidth_of_le x (by decide : 32 ≤ 64), BitVec.setWidth_eq]
  apply AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · x86_norm [headerEffect, narrow]
  · x86_norm [headerEffect, narrow]
    repeat constructor
  · intro i
    cases i <;> x86_norm [headerEffect, narrow]
  · x86_norm [headerEffect, narrow]

end P256.Proofs.Verifying.Combination.Naf.Machine
