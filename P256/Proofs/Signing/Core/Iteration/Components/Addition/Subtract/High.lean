import P256.Proofs.Signing.Core.Iteration.Components.Addition.Subtract.Interface
import P256.Proofs.Common.Field.Operations.Add.Machine.ForgetFlags

set_option autoImplicit false

open P256.Proofs.Program

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)
open P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction (borrow)

namespace P256.Proofs.Signing.Core.Iteration.Components.Addition.Subtract

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def highBytes : List UInt8 :=
  [0x48, 0x8b, 0x49, 0x18, 0x4d, 0x89, 0xc5, 0x49, 0x29, 0xcd, 0x49, 0xc1, 0xff, 0x3f, 0x4d, 0x01, 0xef, 0x4d, 0x89, 0xc5, 0x49, 0xf7, 0xd5, 0x48, 0x89, 0xcd, 0x4c, 0x21, 0xed, 0x49, 0x09, 0xcd, 0x4d, 0x21, 0xfd, 0x49, 0x09, 0xed, 0x49, 0xc1, 0xed, 0x3f, 0x4c, 0x89, 0x2c, 0x24, 0x45, 0x31, 0xed, 0x4c, 0x2b, 0x2c, 0x24]

def highEffect (s : RamState) : Effect :=
  let a := (Operand.reg 8 : Operand 64).read s
  let m := (Operand.mem ((Operand.reg 1 : Operand 64).read s + 24) : Operand 64).read s
  let r := ((Operand.reg 15 : Operand 64).read s).sshiftRight 63 + (a - m)
  let b := borrow a m r
  { rip := 0x113a42
    writes := [⟨(Operand.reg 1 : Operand 64), m⟩,
      ⟨(Operand.reg 15 : Operand 64), r⟩,
      ⟨(Operand.reg 5 : Operand 64), m &&& ~~~a⟩,
      ⟨(Operand.reg 13 : Operand 64), -b⟩,
      ⟨(Operand.mem (stackPtr s) : Operand 64), b⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 2048 in
theorem high_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (BlockPre 0x113a0d) (codeRange 0x113a0d highBytes)
      (Effect.post highEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x113a0d 0x48 (by simp [RexWPrefix]) 1 (.base 1 (.d8 24)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x113a0d highBytes 0 4)
  case pre =>
    intro s hP
    refine ⟨hP.rip, ?_⟩
    exact hP.input 24 (by decide)
  case next =>
    intro s hP
    exact boundary_ne_program hout (inProgram_of_textOffset 0x13a11 (by decide))
  advance_then (mov_r64_r64_effect_step 0x113a11 0x4d 0xc5 (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x113a0d highBytes 4 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13a14 (by decide))
  advance_then (sub_r64_r64_effect_step 0x113a14 0x49 0xcd (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x113a0d highBytes 7 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13a17 (by decide))
  advance_then (P256.Proofs.Common.Instructions.sar_r64_imm8_effect_step 0x113a17 0x49 0xff 63 (by simp [RexWPrefix]) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x113a0d highBytes 10 4)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13a1b (by decide))
  advance_then (add_r64_r64_effect_step 0x113a1b 0x4d 0xef (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x113a0d highBytes 14 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13a1e (by decide))
  advance_then (mov_r64_r64_effect_step 0x113a1e 0x4d 0xc5 (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x113a0d highBytes 17 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13a21 (by decide))
  advance_then (not_r64_effect_step 0x113a21 0x49 0xd5 (by simp [RexWPrefix]) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x113a0d highBytes 20 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13a24 (by decide))
  advance_then (mov_r64_r64_effect_step 0x113a24 0x48 0xcd (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x113a0d highBytes 23 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13a27 (by decide))
  advance_then (and_r64_r64_effect_step 0x113a27 0x4c 0xed (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x113a0d highBytes 26 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13a2a (by decide))
  advance_then (P256.Proofs.Common.Field.FieldNeg.Instructions.or_r64_r64_effect_step 0x113a2a 0x49 0xcd (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x113a0d highBytes 29 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13a2d (by decide))
  advance_then (and_r64_r64_effect_step 0x113a2d 0x4d 0xfd (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x113a0d highBytes 32 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13a30 (by decide))
  advance_then (P256.Proofs.Common.Field.FieldNeg.Instructions.or_r64_r64_effect_step 0x113a30 0x49 0xed (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x113a0d highBytes 35 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13a33 (by decide))
  advance_then (shr_r64_imm8_effect_step 0x113a33 0x49 0xed 63 (by simp [RexWPrefix]) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x113a0d highBytes 38 4)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13a37 (by decide))
  advance_then (mov_m64_r64_effect_step 0x113a37 0x4c (by simp [RexWPrefix]) 5 (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x113a0d highBytes 42 4)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm [BitVec.add_zero]) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm [BitVec.add_zero]
      exact hP.writable
    · x86_norm [BitVec.add_zero]
      exact hP.apart 0x13a37 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [BitVec.add_zero]
      exact hP.apart 0x13a0d 53 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13a3b (by decide))
  advance_then (xor_r32_r32_rex_effect_step 0x113a3b 0x45 0xed (by simp [RexNoWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x113a0d highBytes 46 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_zero]), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13a3e (by decide))
  advance_then (P256.Proofs.Common.Field.Instructions.sub_r64_m64_effect_step 0x113a3e 0x4c (by simp [RexWPrefix]) 5 (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x113a0d highBytes 49 4)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [BitVec.add_zero]) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [BitVec.add_zero]
      exact hP.writable.readable
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13a42 (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [highEffect, borrow, BitVec.add_zero]
  · x86_norm [highEffect, borrow, BitVec.add_zero]
    all_goals simp [gprNumber, modrmRm, shiftCount, Operand.read_reg64,
      gprIndex, modrmReg, BitVec.zero_sub, rexB, rexR]
  · intro i
    cases i <;> exact .inl rfl
  · x86_norm [highEffect]
    simp

end P256.Proofs.Signing.Core.Iteration.Components.Addition.Subtract
