import P256.Proofs.Signing.Core.Iteration.Components.Addition.Output.Selection.Common

set_option autoImplicit false

open P256.Proofs.Program

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction (selectWord)
open P256.Proofs.Common.Instructions (mov_m8_r8_legacy_effect_step)
open P256.Proofs.Common.Instructions.Neg64 (negR64Effect neg_r64_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Signing.Core.Iteration.Components.Addition.Selection

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs



attribute [local x86_local] P256.Proofs.Field.Add.negR64Effect_local storeByteRegister_local
attribute [local x86_compose] negR64Effect lowByte_read_dword
  BitVec.setWidth_setWidth_of_le BitVec.setWidth_eq

def thirdBytes : List UInt8 := [0x88, 0xc, 0x24, 0xf, 0xb6, 0x34, 0x24, 0x4d, 0x31, 0xf1, 0x48, 0xf7, 0xde, 0x4c, 0x21, 0xce, 0x4c, 0x31, 0xf6]

def thirdEffect (s : RamState) : Effect :=
  let a := (Operand.reg 9 : Operand 64).read s
  let b := (Operand.reg 14 : Operand 64).read s
  let flag := (Operand.reg 1 : Operand 8).read s
  let selected := selectWord a b (flag.setWidth 64)
  { rip := 0x113ab1
    writes := [⟨(Operand.reg 9 : Operand 64), a ^^^ b⟩,
      ⟨(Operand.reg 6 : Operand 64), selected⟩,
      ⟨(Operand.mem (stackPtr s) : Operand 8), flag⟩]
    flags := some (xorFlags selected) }

set_option maxHeartbeats 800000 in
set_option maxRecDepth 2048 in
theorem third_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (Pre 0x113a9e) (codeRange 0x113a9e thirdBytes)
      (Effect.post thirdEffect) := by
  advance_begin (show StepEffect _ _ (storeEffect 0x113a9e 3 (storeAddrAt 0x113a9e (.sib 4 none 0 .none) 3) (fun s => (Operand.reg 1 : Operand 8).read s)) from mov_m8_r8_legacy_effect_step 0x113a9e 1 (by decide) (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    refine ⟨h.rip, ?_, ?_⟩
    · x86_norm [BitVec.add_zero]
      exact h.writable
    · x86_norm [BitVec.add_zero]
      exact h.apart 0x13a9e 3 (by decide)
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm [BitVec.add_zero]
    exact h.apart 0x13a9e 19 (by decide)
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0x13aa1 (by decide))
  advance_then (show StepEffect _ _ (movzxR32M8Effect 0x113aa1 4 6 (.sib 4 none 0 .none)) from movzx_r32_m8_effect_step 0x113aa1 6 (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113a9e thirdBytes 3 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [BitVec.add_zero]) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [BitVec.add_zero]
      exact hP.writable.readable
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13aa5 (by decide))
  advance_then (xor_r64_r64_effect_step 0x113aa5 0x4d 0xf1 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x113a9e thirdBytes 7 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13aa8 (by decide))
  advance_then (neg_r64_effect_step 0x113aa8 0x48 0xde (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113a9e thirdBytes 10 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13aab (by decide))
  advance_then (and_r64_r64_effect_step 0x113aab 0x4c 0xce (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x113a9e thirdBytes 13 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13aae (by decide))
  advance_then (xor_r64_r64_effect_step 0x113aae 0x4c 0xf6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x113a9e thirdBytes 16 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13ab1 (by decide))
  apply AdvanceTriple.block_end
  intro s u hp he
  apply he.weaken
  · rfl
  · x86_norm [thirdEffect, selectWord, stackPtr, BitVec.add_zero, gprNumber, rexR, rexB,
      modrmReg, modrmRm, UInt8.toBitVec_ofNat, gprIndex]
    repeat first | apply And.intro | exact Or.inl rfl | exact Or.inr rfl | rfl
  · intro i
    cases i <;> x86_norm [thirdEffect, selectWord, stackPtr, BitVec.add_zero, gprNumber, rexR, rexB,
      modrmReg, modrmRm, UInt8.toBitVec_ofNat, gprIndex]
    all_goals first | exact Or.inl rfl | exact Or.inr rfl | rfl
  · x86_norm [thirdEffect, selectWord, stackPtr, BitVec.add_zero, gprNumber, rexR, rexB,
      modrmReg, modrmRm, UInt8.toBitVec_ofNat, gprIndex]
    repeat first | apply And.intro | exact Or.inl rfl | exact Or.inr rfl | rfl

end P256.Proofs.Signing.Core.Iteration.Components.Addition.Selection
