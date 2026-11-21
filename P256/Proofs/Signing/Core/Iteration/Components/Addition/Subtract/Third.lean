import P256.Proofs.Signing.Core.Iteration.Components.Addition.Subtract.Interface
import P256.Proofs.Common.Field.Operations.Add.Machine.ForgetFlags

set_option autoImplicit false

open P256.Proofs.Program

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)
open P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction (borrow)

namespace P256.Proofs.Signing.Core.Iteration.Components.Addition.Subtract

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def thirdBytes : List UInt8 :=
  [0x48, 0x8b, 0x69, 0x10, 0x4d, 0x89, 0xcd, 0x49, 0x29, 0xed, 0x49, 0xc1, 0xfe, 0x3f, 0x4d, 0x01, 0xee, 0x4d, 0x89, 0xcd, 0x49, 0xf7, 0xd5, 0x49, 0x89, 0xef, 0x4d, 0x21, 0xef, 0x49, 0x09, 0xed, 0x4d, 0x21, 0xf5, 0x4d, 0x09, 0xfd, 0x49, 0xc1, 0xed, 0x3f, 0x4c, 0x89, 0x2c, 0x24, 0x45, 0x31, 0xff, 0x4c, 0x2b, 0x3c, 0x24]

def thirdEffect (s : RamState) : Effect :=
  let a := (Operand.reg 9 : Operand 64).read s
  let m := (Operand.mem ((Operand.reg 1 : Operand 64).read s + 16) : Operand 64).read s
  let r := ((Operand.reg 14 : Operand 64).read s).sshiftRight 63 + (a - m)
  let b := borrow a m r
  { rip := 0x113a0d
    writes := [⟨(Operand.reg 5 : Operand 64), m⟩,
      ⟨(Operand.reg 14 : Operand 64), r⟩,
      ⟨(Operand.reg 13 : Operand 64), b⟩,
      ⟨(Operand.reg 15 : Operand 64), -b⟩,
      ⟨(Operand.mem (stackPtr s) : Operand 64), b⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 2048 in
theorem third_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (BlockPre 0x1139d8) (codeRange 0x1139d8 thirdBytes)
      (Effect.post thirdEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x1139d8 0x48 (by simp [RexWPrefix]) 5 (.base 1 (.d8 16)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x1139d8 thirdBytes 0 4)
  case pre =>
    intro s hP
    refine ⟨hP.rip, ?_⟩
    exact hP.input 16 (by decide)
  case next =>
    intro s hP
    exact boundary_ne_program hout (inProgram_of_textOffset 0x139dc (by decide))
  advance_then (mov_r64_r64_effect_step 0x1139dc 0x4d 0xcd (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x1139d8 thirdBytes 4 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x139df (by decide))
  advance_then (sub_r64_r64_effect_step 0x1139df 0x49 0xed (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x1139d8 thirdBytes 7 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x139e2 (by decide))
  advance_then (P256.Proofs.Common.Instructions.sar_r64_imm8_effect_step 0x1139e2 0x49 0xfe 63 (by simp [RexWPrefix]) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x1139d8 thirdBytes 10 4)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x139e6 (by decide))
  advance_then (add_r64_r64_effect_step 0x1139e6 0x4d 0xee (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x1139d8 thirdBytes 14 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x139e9 (by decide))
  advance_then (mov_r64_r64_effect_step 0x1139e9 0x4d 0xcd (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x1139d8 thirdBytes 17 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x139ec (by decide))
  advance_then (not_r64_effect_step 0x1139ec 0x49 0xd5 (by simp [RexWPrefix]) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x1139d8 thirdBytes 20 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x139ef (by decide))
  advance_then (mov_r64_r64_effect_step 0x1139ef 0x49 0xef (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x1139d8 thirdBytes 23 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x139f2 (by decide))
  advance_then (and_r64_r64_effect_step 0x1139f2 0x4d 0xef (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x1139d8 thirdBytes 26 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x139f5 (by decide))
  advance_then (P256.Proofs.Common.Field.FieldNeg.Instructions.or_r64_r64_effect_step 0x1139f5 0x49 0xed (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x1139d8 thirdBytes 29 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x139f8 (by decide))
  advance_then (and_r64_r64_effect_step 0x1139f8 0x4d 0xf5 (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x1139d8 thirdBytes 32 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x139fb (by decide))
  advance_then (P256.Proofs.Common.Field.FieldNeg.Instructions.or_r64_r64_effect_step 0x1139fb 0x4d 0xfd (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x1139d8 thirdBytes 35 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x139fe (by decide))
  advance_then (shr_r64_imm8_effect_step 0x1139fe 0x49 0xed 63 (by simp [RexWPrefix]) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x1139d8 thirdBytes 38 4)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13a02 (by decide))
  advance_then (mov_m64_r64_effect_step 0x113a02 0x4c (by simp [RexWPrefix]) 5 (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x1139d8 thirdBytes 42 4)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm [BitVec.add_zero]) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm [BitVec.add_zero]
      exact hP.writable
    · x86_norm [BitVec.add_zero]
      exact hP.apart 0x13a02 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [BitVec.add_zero]
      exact hP.apart 0x139d8 53 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13a06 (by decide))
  advance_then (xor_r32_r32_rex_effect_step 0x113a06 0x45 0xff (by simp [RexNoWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x1139d8 thirdBytes 46 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13a09 (by decide))
  advance_then (P256.Proofs.Common.Field.Instructions.sub_r64_m64_effect_step 0x113a09 0x4c (by simp [RexWPrefix]) 7 (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x1139d8 thirdBytes 49 4)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [BitVec.add_zero]) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [BitVec.add_zero]
      exact hP.writable.readable
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13a0d (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [thirdEffect, borrow, BitVec.add_zero]
  · x86_norm [thirdEffect, borrow, BitVec.add_zero]
    all_goals simp [gprNumber, modrmRm, shiftCount, Operand.read_reg64,
      gprIndex, modrmReg, BitVec.zero_sub, rexB, rexR]
  · intro i
    cases i <;> exact .inl rfl
  · x86_norm [thirdEffect]
    simp

end P256.Proofs.Signing.Core.Iteration.Components.Addition.Subtract
