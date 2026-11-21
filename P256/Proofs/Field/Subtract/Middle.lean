import P256.Proofs.SecretKeyFromBytes.Scalar.Borrow
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Not.Generated.R.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Movs.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple
import P256.Proofs.Field.Montgomery.Reduction.Slot
import P256.Proofs.Field.Montgomery.Reduction.TailCorrespondence
import P256.Proofs.Common.Field.Montgomery.Schoolbook.CarryCompose
import P256.Proofs.Common.Instructions.AddByte
import P256.Proofs.Common.Field.Operations.Neg.Borrow.Or
import P256.Proofs.Common.Field.Operations.Add.Machine.ForgetFlags
import P256.Proofs.Common.Encoding.Serialize.Convert.Compose
import P256.Proofs.Field.Subtract.Arithmetic

set_option autoImplicit false

open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Field.Subtract

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.SecretKeyFromBytes.Scalar (Limbs)
open P256.Proofs.Field.Montgomery.Reduction
open P256.Spec.Program.Routines
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def borrowMiddleBytes : List UInt8 :=
  [0x4d, 0x89, 0xc6, 0x49, 0x29, 0xde, 0x48, 0xc1, 0xfa, 0x3f, 0x4c, 0x1, 0xf2, 0x49, 0xf7, 0xd0, 0x49, 0x89, 0xde, 0x4d, 0x21, 0xc6, 0x49, 0x9, 0xd8, 0x49, 0x21, 0xd0, 0x4d, 0x9, 0xf0, 0x49, 0xc1, 0xe8, 0x3f, 0x4c, 0x89, 0x4, 0x24, 0x49, 0x89, 0xe0, 0x45, 0x31, 0xc0]

def borrowMiddleEffect (s : RamState) : Effect :=
  let a := (Operand.reg 8 : Operand 64).read s
  let b := (Operand.reg 3 : Operand 64).read s
  let r := ((Operand.reg 2 : Operand 64).read s).sshiftRight 63 + (a-b)
  let q := (((~~~a ||| b) &&& r) ||| (b &&& ~~~a)) >>> 63
  { rip := 0x113f9b
    writes := [⟨(Operand.reg 14 : Operand 64), b &&& ~~~a⟩,
      ⟨(Operand.reg 2 : Operand 64), r⟩,
      ⟨(Operand.reg 8 : Operand 64), 0⟩,
      ⟨(Operand.mem (stackPtr s) : Operand 64), q⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

set_option maxHeartbeats 1600000 in
theorem borrow_middle_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (BorrowSlotPre 0x113f6e)
      (codeRange 0x113f6e borrowMiddleBytes) (Effect.post borrowMiddleEffect) := by
  advance_begin (mov_r64_r64_effect_step 0x113f6e 0x4d 0xc6 (by unfold RexWPrefix; decide +kernel) rfl)
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0x13f71 (by decide +kernel))
  advance_then (sub_r64_r64_effect_step 0x113f71 0x49 0xde (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x113f6e borrowMiddleBytes 3 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13f74 (by decide +kernel))
  advance_then (P256.Proofs.Common.Instructions.sar_r64_imm8_effect_step 0x113f74 0x48 0xfa 63 (by unfold RexWPrefix; decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113f6e borrowMiddleBytes 6 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [P256.Proofs.Common.Instructions.sarR64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13f78 (by decide +kernel))
  advance_then (add_r64_r64_effect_step 0x113f78 0x4c 0xf2 (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x113f6e borrowMiddleBytes 10 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13f7b (by decide +kernel))
  advance_then (not_r64_effect_step 0x113f7b 0x49 0xd0 (by unfold RexWPrefix; decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113f6e borrowMiddleBytes 13 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13f7e (by decide +kernel))
  advance_then (mov_r64_r64_effect_step 0x113f7e 0x49 0xde (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x113f6e borrowMiddleBytes 16 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13f81 (by decide +kernel))
  advance_then (and_r64_r64_effect_step 0x113f81 0x4d 0xc6 (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x113f6e borrowMiddleBytes 19 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13f84 (by decide +kernel))
  advance_then (P256.Proofs.Common.Field.FieldNeg.Instructions.or_r64_r64_effect_step 0x113f84 0x49 0xd8 (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x113f6e borrowMiddleBytes 22 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13f87 (by decide +kernel))
  advance_then (and_r64_r64_effect_step 0x113f87 0x49 0xd0 (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x113f6e borrowMiddleBytes 25 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13f8a (by decide +kernel))
  advance_then (P256.Proofs.Common.Field.FieldNeg.Instructions.or_r64_r64_effect_step 0x113f8a 0x4d 0xf0 (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x113f6e borrowMiddleBytes 28 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13f8d (by decide +kernel))
  advance_then (shr_r64_imm8_effect_step 0x113f8d 0x49 0xe8 63 (by unfold RexWPrefix; decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113f6e borrowMiddleBytes 31 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13f91 (by decide +kernel))
  advance_then (mov_m64_r64_effect_step 0x113f91 0x4c (by unfold RexWPrefix; decide +kernel) 0 (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113f6e borrowMiddleBytes 35 4
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm [BitVec.add_zero]
      exact hP.writable
    · x86_norm [BitVec.add_zero]
      exact hP.apart 0x13f91 4 (by decide +kernel)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [BitVec.add_zero]
      exact hP.apart 0x13f6e 45 (by decide +kernel)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13f95 (by decide +kernel))
  advance_then (mov_r64_r64_effect_step 0x113f95 0x49 0xe0 (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x113f6e borrowMiddleBytes 39 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13f98 (by decide +kernel))
  advance_then (xor_r32_r32_rex_effect_step 0x113f98 0x45 0xc0 (by unfold RexNoWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x113f6e borrowMiddleBytes 42 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13f9b (by decide +kernel))
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [borrowMiddleEffect, stackPtr, BitVec.xor_self, BitVec.zero_sub, BitVec.add_zero]
    all_goals try simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    all_goals (repeat' constructor)
  · x86_norm [borrowMiddleEffect, stackPtr, BitVec.xor_self, BitVec.zero_sub, BitVec.add_zero]
    all_goals try simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    all_goals (repeat' constructor)
  · intro i; cases i <;> x86_norm [borrowMiddleEffect, stackPtr, BitVec.xor_self, BitVec.zero_sub, BitVec.add_zero]
    all_goals try simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    all_goals (repeat' constructor)
  · x86_norm [borrowMiddleEffect, stackPtr, BitVec.xor_self, BitVec.zero_sub, BitVec.add_zero]
    all_goals try simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    all_goals (repeat' constructor)

theorem borrowMiddleBytes_code :
    P256.Spec.Program.Extracted.textBytes.toListFrom 0x13f6e 45 = borrowMiddleBytes := by
  decide +kernel

end P256.Proofs.Field.Subtract
