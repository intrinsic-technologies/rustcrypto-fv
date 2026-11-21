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

def yThirdSetupBytes : List UInt8 :=
  [72, 137, 124, 36, 16, 49, 255, 72, 43, 124, 36, 16, 72, 193, 255, 63]

def yThirdSetupEffect (s : RamState) : Effect :=
  { rip := 0x1106bf
    writes := [⟨(.mem (stackPtr s + 16) : Operand 64), (Operand.reg 7 : Operand 64).read s⟩,
      ⟨(.reg 7 : Operand 64), (-((Operand.reg 7 : Operand 64).read s)).sshiftRight 63⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem y_third_setup_correct [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (BorrowPre 0x1106af)
      (codeRange 0x1106af yThirdSetupBytes) (Effect.post yThirdSetupEffect) := by
  advance_begin (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1106af 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    exact ⟨h.rip, h.writable, h.apart 0x106af 5 (by decide)⟩
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm
    exact h.apart 0x106af 16 (by decide)
  case next =>
    intro _ _
    exact boundary_ne_program outside (inProgram_of_textOffset 0x106b4 (by decide))
  advance_then (xor_r32_r32_effect_step 0x1106b4 0xff rfl)
  case sub => exact codeRange_slice_subset 0x1106af yThirdSetupBytes 5 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x106b6 (by decide))
  advance_then (sub_r64_m64_effect_step 0x1106b6 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1106af yThirdSetupBytes 7 5
  case mid =>
    intro s t hP hH hO
    refine ⟨X86Proofs.LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable.1
    · exact Effect.Avoids.of_noMem (by simp [subR64M64Effect_components, Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x106bb (by decide))
  advance_then (sar_r64_imm8_effect_step 0x1106bb 0x48 0xff 63 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1106af yThirdSetupBytes 12 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · exact Effect.Avoids.of_noMem (by simp [sarR64Effect_components, Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x106bf (by decide))
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · rfl
  · x86_norm [yThirdSetupEffect, stackPtr, Operand.read_reg64, BitVec.xor_self,
      BitVec.zero_sub, BitVec.setWidth_zero]
    all_goals first | (repeat first | constructor | rfl); done | simp [gprNumber, rexR, modrmRm, modrmReg, shiftCount, BitVec.xor_self, BitVec.zero_sub]
  · intro i; cases i <;> x86_norm [yThirdSetupEffect]
  · x86_norm [yThirdSetupEffect, stackPtr, Operand.read_reg64]
    all_goals first | (repeat first | constructor | rfl); done | simp [gprNumber, rexR, modrmRm, modrmReg, shiftCount, BitVec.xor_self, BitVec.zero_sub]

end P256.Proofs.Sec1.Affine.Uncompressed.Parse.Canonical
