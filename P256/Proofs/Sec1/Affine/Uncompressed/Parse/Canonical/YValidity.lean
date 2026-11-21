import P256.Proofs.Sec1.Affine.Uncompressed.Parse.Canonical.Slot
import P256.Proofs.Common.EffectCompose.ByteLogic
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple
import P256.Proofs.Common.EffectCompose.Advance

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Parse.Canonical

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions.ByteLogic (andR8Imm8Effect and_r8_imm8_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

def yValidityBytes : List UInt8 :=
  [72, 137, 68, 36, 16, 68, 15, 182, 116, 36, 16, 65, 128, 230, 1]

def yValidityEffect (s : RamState) : Effect :=
  let x := (Operand.reg 0 : Operand 64).read s
  { rip := 0x110704
    writes := [⟨(.mem (stackPtr s + 16) : Operand 64), x⟩,
      ⟨(.reg 14 : Operand 64), (x.setWidth 8 &&& 1).setWidth 64⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem y_validity_correct [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (BorrowPre 0x1106f5)
      (codeRange 0x1106f5 yValidityBytes) (Effect.post yValidityEffect) := by
  advance_begin (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any
    0x1106f5 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 16))
    (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    exact ⟨h.rip, h.writable, h.apart 0x106f5 5 (by decide)⟩
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm
    exact h.apart 0x106f5 15 (by decide)
  case next =>
    intro _ _
    exact boundary_ne_program outside (inProgram_of_textOffset 0x106fa (by decide))
  advance_then (movzx_r32_m8_rex_effect_step 0x1106fa 0x44 (by simp [RexNoWPrefix]) 6 (.sib 4 none 0 (.d8 16))
    (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1106f5 yValidityBytes 5 6
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      change MemReadable s (stackPtr s + 16) 1
      exact ⟨by have h := hP.writable.1.low; omega,
        fun i hi => hP.writable.1.mem i (by omega)⟩
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10700 (by decide))
  advance_then (and_r8_imm8_effect_step 0x110700 0x41 0xe6 1 (by simp [RexPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1106f5 yValidityBytes 11 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem
      (by simp [andR8Imm8Effect, Effect.components, Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x10704 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · rfl
  · x86_norm [yValidityEffect, stackPtr, Operand.read_reg64]
    change s.regValue .rax = s.regValue .rax ∧
      ((s.regValue .rax).setWidth 8 &&& 1).setWidth 64 =
        mergeGPR 8 ((((s.regValue .rax).setWidth 8).setWidth 64).setWidth 8 &&& 1)
          (((s.regValue .rax).setWidth 8).setWidth 64)
    refine ⟨rfl, ?_⟩
    simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64)]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [mergeGPR, show (8 : Nat) ≠ 32 by decide, ↓reduceIte]
    rw [getLsbD_setSlice _ _ _ _ i hi]
    by_cases h : i < 8 <;> simp [BitVec.getLsbD_setWidth, h, hi]
  · intro i; cases i <;> x86_norm [yValidityEffect]
  · x86_norm [yValidityEffect, stackPtr, Operand.read_reg64]

end P256.Proofs.Sec1.Affine.Uncompressed.Parse.Canonical
