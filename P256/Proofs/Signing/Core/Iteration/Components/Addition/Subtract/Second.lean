import P256.Proofs.Signing.Core.Iteration.Components.Addition.Subtract.Interface
import P256.Proofs.Common.Field.Operations.Add.Machine.ForgetFlags

set_option autoImplicit false

open P256.Proofs.Program

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)
open P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction (borrow)

namespace P256.Proofs.Signing.Core.Iteration.Components.Addition.Subtract

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def secondBytes : List UInt8 :=
  [0x4c, 0x8b, 0x71, 0x8, 0x4d, 0x89, 0xd7, 0x4d, 0x29, 0xf7, 0x48, 0xc1, 0xfe, 0x3f, 0x4c, 0x1, 0xfe, 0x4d, 0x89, 0xd7, 0x49, 0xf7, 0xd7, 0x4d, 0x89, 0xf5, 0x4d, 0x21, 0xfd, 0x4d, 0x9, 0xf7, 0x49, 0x21, 0xf7, 0x4d, 0x9, 0xef, 0x49, 0xc1, 0xef, 0x3f, 0x4c, 0x89, 0x3c, 0x24, 0x45, 0x31, 0xf6, 0x4c, 0x2b, 0x34, 0x24]

def secondEffect (s : RamState) : Effect :=
  let a := (Operand.reg 10 : Operand 64).read s
  let m := (Operand.mem ((Operand.reg 1 : Operand 64).read s + 8) : Operand 64).read s
  let r := ((Operand.reg 6 : Operand 64).read s).sshiftRight 63 + (a - m)
  let b := borrow a m r
  { rip := 0x1139d8
    writes := [⟨(Operand.reg 14 : Operand 64), -b⟩,
      ⟨(Operand.reg 15 : Operand 64), b⟩,
      ⟨(Operand.reg 6 : Operand 64), r⟩,
      ⟨(Operand.reg 13 : Operand 64), m &&& ~~~a⟩,
      ⟨(Operand.mem (stackPtr s) : Operand 64), b⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 2048 in
theorem second_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (BlockPre 0x1139a3) (codeRange 0x1139a3 secondBytes)
      (Effect.post secondEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x1139a3 0x4c (by simp [RexWPrefix]) 6 (.base 1 (.d8 8)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x1139a3 secondBytes 0 4)
  case pre =>
    intro s hP
    refine ⟨hP.rip, ?_⟩
    exact hP.input 8 (by decide)
  case next =>
    intro s hP
    exact boundary_ne_program hout (inProgram_of_textOffset 0x139a7 (by decide))
  advance_then (mov_r64_r64_effect_step 0x1139a7 0x4d 0xd7 (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x1139a3 secondBytes 4 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x139aa (by decide))
  advance_then (sub_r64_r64_effect_step 0x1139aa 0x4d 0xf7 (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x1139a3 secondBytes 7 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x139ad (by decide))
  advance_then (P256.Proofs.Common.Instructions.sar_r64_imm8_effect_step 0x1139ad 0x48 0xfe 63 (by simp [RexWPrefix]) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x1139a3 secondBytes 10 4)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x139b1 (by decide))
  advance_then (add_r64_r64_effect_step 0x1139b1 0x4c 0xfe (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x1139a3 secondBytes 14 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x139b4 (by decide))
  advance_then (mov_r64_r64_effect_step 0x1139b4 0x4d 0xd7 (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x1139a3 secondBytes 17 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x139b7 (by decide))
  advance_then (not_r64_effect_step 0x1139b7 0x49 0xd7 (by simp [RexWPrefix]) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x1139a3 secondBytes 20 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x139ba (by decide))
  advance_then (mov_r64_r64_effect_step 0x1139ba 0x4d 0xf5 (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x1139a3 secondBytes 23 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x139bd (by decide))
  advance_then (and_r64_r64_effect_step 0x1139bd 0x4d 0xfd (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x1139a3 secondBytes 26 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x139c0 (by decide))
  advance_then (P256.Proofs.Common.Field.FieldNeg.Instructions.or_r64_r64_effect_step 0x1139c0 0x4d 0xf7 (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x1139a3 secondBytes 29 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x139c3 (by decide))
  advance_then (and_r64_r64_effect_step 0x1139c3 0x49 0xf7 (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x1139a3 secondBytes 32 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x139c6 (by decide))
  advance_then (P256.Proofs.Common.Field.FieldNeg.Instructions.or_r64_r64_effect_step 0x1139c6 0x4d 0xef (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x1139a3 secondBytes 35 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x139c9 (by decide))
  advance_then (shr_r64_imm8_effect_step 0x1139c9 0x49 0xef 63 (by simp [RexWPrefix]) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x1139a3 secondBytes 38 4)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x139cd (by decide))
  advance_then (mov_m64_r64_effect_step 0x1139cd 0x4c (by simp [RexWPrefix]) 7 (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x1139a3 secondBytes 42 4)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm [BitVec.add_zero]) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm [BitVec.add_zero]
      exact hP.writable
    · x86_norm [BitVec.add_zero]
      exact hP.apart 0x139cd 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [BitVec.add_zero]
      exact hP.apart 0x139a3 53 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x139d1 (by decide))
  advance_then (xor_r32_r32_rex_effect_step 0x1139d1 0x45 0xf6 (by simp [RexNoWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x1139a3 secondBytes 46 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x139d4 (by decide))
  advance_then (P256.Proofs.Common.Field.Instructions.sub_r64_m64_effect_step 0x1139d4 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x1139a3 secondBytes 49 4)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [BitVec.add_zero]) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [BitVec.add_zero]
      exact hP.writable.readable
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x139d8 (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [secondEffect, borrow, BitVec.add_zero]
  · x86_norm [secondEffect, borrow, BitVec.add_zero]
    all_goals simp [gprNumber, modrmRm, shiftCount, Operand.read_reg64,
      gprIndex, modrmReg, BitVec.zero_sub, rexB, rexR]
  · intro i
    cases i <;> exact .inl rfl
  · x86_norm [secondEffect]
    simp

end P256.Proofs.Signing.Core.Iteration.Components.Addition.Subtract
