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

def xHighSetupBytes : List UInt8 :=
  [72, 137, 76, 36, 16, 76, 43, 108, 36, 16, 73, 193, 253, 63]

def xHighSetupEffect (s : RamState) : Effect :=
  { rip := 0x1108ba
    writes := [⟨(.mem (stackPtr s + 16) : Operand 64), (Operand.reg 1 : Operand 64).read s⟩,
      ⟨(.reg 13 : Operand 64), (((Operand.reg 13 : Operand 64).read s) - ((Operand.reg 1 : Operand 64).read s)).sshiftRight 63⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem x_high_setup_correct [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (BorrowPre 0x1108ac)
      (codeRange 0x1108ac xHighSetupBytes) (Effect.post xHighSetupEffect) := by
  advance_begin (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1108ac 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    exact ⟨h.rip, h.writable, h.apart 0x108ac 5 (by decide)⟩
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm
    exact h.apart 0x108ac 14 (by decide)
  case next =>
    intro _ _
    exact boundary_ne_program outside (inProgram_of_textOffset 0x108b1 (by decide))
  advance_then (sub_r64_m64_effect_step 0x1108b1 0x4c (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1108ac xHighSetupBytes 5 5
  case mid =>
    intro s t hP hH hO
    refine ⟨X86Proofs.LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable.1
    · exact Effect.Avoids.of_noMem (by simp [subR64M64Effect_components, Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x108b6 (by decide))
  advance_then (sar_r64_imm8_effect_step 0x1108b6 0x49 0xfd 63 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1108ac xHighSetupBytes 10 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · exact Effect.Avoids.of_noMem (by simp [sarR64Effect_components, Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x108ba (by decide))
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · rfl
  · x86_norm [xHighSetupEffect, stackPtr, Operand.read_reg64, BitVec.xor_self,
      BitVec.zero_sub, BitVec.setWidth_zero]
    all_goals repeat first | constructor | rfl
  · intro i; cases i <;> x86_norm [xHighSetupEffect]
  · x86_norm [xHighSetupEffect, stackPtr, Operand.read_reg64]
    all_goals repeat first | constructor | rfl

end P256.Proofs.Sec1.Affine.Uncompressed.Parse.Canonical
