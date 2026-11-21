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

def xThirdSetupBytes : List UInt8 :=
  [72, 137, 116, 36, 16, 49, 246, 72, 43, 116, 36, 16, 72, 193, 254, 63]

def xThirdSetupEffect (s : RamState) : Effect :=
  { rip := 0x11089f
    writes := [⟨(.mem (stackPtr s + 16) : Operand 64), (Operand.reg 6 : Operand 64).read s⟩,
      ⟨(.reg 6 : Operand 64), (-((Operand.reg 6 : Operand 64).read s)).sshiftRight 63⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem x_third_setup_correct [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (BorrowPre 0x11088f)
      (codeRange 0x11088f xThirdSetupBytes) (Effect.post xThirdSetupEffect) := by
  advance_begin (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x11088f 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    exact ⟨h.rip, h.writable, h.apart 0x1088f 5 (by decide)⟩
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm
    exact h.apart 0x1088f 16 (by decide)
  case next =>
    intro _ _
    exact boundary_ne_program outside (inProgram_of_textOffset 0x10894 (by decide))
  advance_then (xor_r32_r32_effect_step 0x110894 0xf6 rfl)
  case sub => exact codeRange_slice_subset 0x11088f xThirdSetupBytes 5 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10896 (by decide))
  advance_then (sub_r64_m64_effect_step 0x110896 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11088f xThirdSetupBytes 7 5
  case mid =>
    intro s t hP hH hO
    refine ⟨X86Proofs.LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable.1
    · exact Effect.Avoids.of_noMem (by simp [subR64M64Effect_components, Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1089b (by decide))
  advance_then (sar_r64_imm8_effect_step 0x11089b 0x48 0xfe 63 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11088f xThirdSetupBytes 12 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · exact Effect.Avoids.of_noMem (by simp [sarR64Effect_components, Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1089f (by decide))
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · rfl
  · x86_norm [xThirdSetupEffect, stackPtr, Operand.read_reg64, BitVec.xor_self,
      BitVec.zero_sub, BitVec.setWidth_zero]
    all_goals first | (repeat first | constructor | rfl); done | simp [gprNumber, rexR, modrmRm, modrmReg, shiftCount, BitVec.xor_self, BitVec.zero_sub]
  · intro i; cases i <;> x86_norm [xThirdSetupEffect]
  · x86_norm [xThirdSetupEffect, stackPtr, Operand.read_reg64]
    all_goals first | (repeat first | constructor | rfl); done | simp [gprNumber, rexR, modrmRm, modrmReg, shiftCount, BitVec.xor_self, BitVec.zero_sub]

end P256.Proofs.Sec1.Affine.Uncompressed.Parse.Canonical
