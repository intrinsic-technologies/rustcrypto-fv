import P256.Proofs.Signing.Core.Iteration.Components.Addition.Subtract.Interface
import P256.Proofs.Common.Field.Operations.Add.Machine.ForgetFlags

set_option autoImplicit false

open P256.Proofs.Program

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)
open P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction (borrow)

namespace P256.Proofs.Signing.Core.Iteration.Components.Addition.Subtract

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def lowBytes : List UInt8 :=
  [0x48, 0x8b, 0x1, 0x4c, 0x89, 0xda, 0x48, 0x29, 0xc2, 0x4c, 0x89, 0xde, 0x48, 0xf7, 0xd6, 0x49, 0x89, 0xc6, 0x49, 0x21, 0xf6, 0x48, 0x9, 0xc6, 0x48, 0x21, 0xd6, 0x4c, 0x9, 0xf6, 0x48, 0xc1, 0xee, 0x3f, 0x48, 0x89, 0x34, 0x24, 0x48, 0x89, 0xe0, 0x31, 0xf6, 0x48, 0x2b, 0x34, 0x24]

def lowEffect (s : RamState) : Effect :=
  let a := (Operand.reg 11 : Operand 64).read s
  let m := (Operand.mem ((Operand.reg 1 : Operand 64).read s) : Operand 64).read s
  let r := a - m
  let b := borrow a m r
  { rip := 0x1139a3
    writes := [⟨(Operand.reg 0 : Operand 64), stackPtr s⟩,
      ⟨(Operand.reg 2 : Operand 64), r⟩,
      ⟨(Operand.reg 6 : Operand 64), -b⟩,
      ⟨(Operand.reg 14 : Operand 64), m &&& ~~~a⟩,
      ⟨(Operand.mem (stackPtr s) : Operand 64), b⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 2048 in
theorem low_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (BlockPre 0x113974) (codeRange 0x113974 lowBytes)
      (Effect.post lowEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x113974 0x48 (by simp [RexWPrefix]) 0 (.base 1 .none) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x113974 lowBytes 0 3)
  case pre =>
    intro s hP
    refine ⟨hP.rip, ?_⟩
    exact hP.input 0 (by decide)
  case next =>
    intro s hP
    exact boundary_ne_program hout (inProgram_of_textOffset 0x13977 (by decide))
  advance_then (mov_r64_r64_effect_step 0x113977 0x4c 0xda (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x113974 lowBytes 3 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1397a (by decide))
  advance_then (sub_r64_r64_effect_step 0x11397a 0x48 0xc2 (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x113974 lowBytes 6 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1397d (by decide))
  advance_then (mov_r64_r64_effect_step 0x11397d 0x4c 0xde (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x113974 lowBytes 9 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13980 (by decide))
  advance_then (not_r64_effect_step 0x113980 0x48 0xd6 (by simp [RexWPrefix]) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x113974 lowBytes 12 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13983 (by decide))
  advance_then (mov_r64_r64_effect_step 0x113983 0x49 0xc6 (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x113974 lowBytes 15 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13986 (by decide))
  advance_then (and_r64_r64_effect_step 0x113986 0x49 0xf6 (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x113974 lowBytes 18 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13989 (by decide))
  advance_then (P256.Proofs.Common.Field.FieldNeg.Instructions.or_r64_r64_effect_step 0x113989 0x48 0xc6 (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x113974 lowBytes 21 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1398c (by decide))
  advance_then (and_r64_r64_effect_step 0x11398c 0x48 0xd6 (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x113974 lowBytes 24 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1398f (by decide))
  advance_then (P256.Proofs.Common.Field.FieldNeg.Instructions.or_r64_r64_effect_step 0x11398f 0x4c 0xf6 (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x113974 lowBytes 27 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13992 (by decide))
  advance_then (shr_r64_imm8_effect_step 0x113992 0x48 0xee 63 (by simp [RexWPrefix]) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x113974 lowBytes 30 4)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13996 (by decide))
  advance_then (mov_m64_r64_effect_step 0x113996 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x113974 lowBytes 34 4)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm [BitVec.add_zero]) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm [BitVec.add_zero]
      exact hP.writable
    · x86_norm [BitVec.add_zero]
      exact hP.apart 0x13996 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [BitVec.add_zero]
      exact hP.apart 0x13974 47 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1399a (by decide))
  advance_then (mov_r64_r64_effect_step 0x11399a 0x48 0xe0 (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x113974 lowBytes 38 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1399d (by decide))
  advance_then (xor_r32_r32_effect_step 0x11399d 0xf6 rfl)
  try (case sub => exact codeRange_slice_subset 0x113974 lowBytes 41 2)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1399f (by decide))
  advance_then (P256.Proofs.Common.Field.Instructions.sub_r64_m64_effect_step 0x11399f 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x113974 lowBytes 43 4)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [BitVec.add_zero]) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [BitVec.add_zero]
      exact hP.writable.readable
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x139a3 (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [lowEffect, borrow, BitVec.add_zero]
  · x86_norm [lowEffect, borrow, BitVec.add_zero]
    all_goals simp [gprNumber, shiftCount, Operand.read_reg64,
      gprIndex, modrmReg, BitVec.zero_sub, rexR]
  · intro i
    cases i <;> exact .inl rfl
  · x86_norm [lowEffect]
    simp

end P256.Proofs.Signing.Core.Iteration.Components.Addition.Subtract
