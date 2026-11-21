import P256.Proofs.Sec1.Affine.Uncompressed.Parse.Canonical.Slot
import P256.Proofs.SecretKeyFromBytes.Scalar.Borrow
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Memory

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Parse.Canonical

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)
open P256.Proofs.Common.Field.Instructions (subR64M64Effect_components sub_r64_m64_effect_step)
open P256.Proofs.Common.Instructions (sarR64Effect_components sar_r64_imm8_effect_step)

def ySecondSetupBytes : List UInt8 :=
  [72, 137, 84, 36, 16, 72, 141, 84, 36, 16, 69, 49, 192, 76, 43, 68, 36, 16, 73, 193, 248, 63]

def ySecondSetupEffect (s : RamState) : Effect :=
  { rip := 0x110695
    writes := [⟨(.mem (stackPtr s + 16) : Operand 64), (Operand.reg 2 : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), stackPtr s + 16⟩,
      ⟨(.reg 8 : Operand 64), (-((Operand.reg 2 : Operand 64).read s)).sshiftRight 63⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem y_second_setup_correct [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (BorrowPre 0x11067f)
      (codeRange 0x11067f ySecondSetupBytes) (Effect.post ySecondSetupEffect) := by
  advance_begin (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x11067f 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    exact ⟨h.rip, h.writable, h.apart 0x1067f 5 (by decide)⟩
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm
    exact h.apart 0x1067f 22 (by decide)
  case next =>
    intro _ _
    exact boundary_ne_program outside (inProgram_of_textOffset 0x10684 (by decide))
  advance_then (lea_r64_effect_step 0x110684 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11067f ySecondSetupBytes 5 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10689 (by decide))
  advance_then (xor_r32_r32_rex_effect_step 0x110689 0x45 0xc0 (by simp [RexNoWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x11067f ySecondSetupBytes 10 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1068c (by decide))
  advance_then (sub_r64_m64_effect_step 0x11068c 0x4c (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11067f ySecondSetupBytes 13 5
  case mid =>
    intro s t hP hH hO
    refine ⟨X86Proofs.LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable.1
    · exact Effect.Avoids.of_noMem (by simp [subR64M64Effect_components, Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10691 (by decide))
  advance_then (sar_r64_imm8_effect_step 0x110691 0x49 0xf8 63 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11067f ySecondSetupBytes 18 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · exact Effect.Avoids.of_noMem (by simp [sarR64Effect_components, Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10695 (by decide))
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · rfl
  · x86_norm [ySecondSetupEffect, stackPtr, Operand.read_reg64, BitVec.xor_self,
      BitVec.zero_sub, BitVec.setWidth_zero]
    all_goals first | (repeat first | constructor | rfl); done | simp [gprNumber, rexR, rexB, modrmRm, modrmReg, shiftCount, BitVec.xor_self, BitVec.zero_sub]
  · intro i; cases i <;> x86_norm [ySecondSetupEffect]
  · x86_norm [ySecondSetupEffect, stackPtr, Operand.read_reg64]
    all_goals first | (repeat first | constructor | rfl); done | simp [gprNumber, rexR, rexB, modrmRm, modrmReg, shiftCount, BitVec.xor_self, BitVec.zero_sub]

end P256.Proofs.Sec1.Affine.Uncompressed.Parse.Canonical
