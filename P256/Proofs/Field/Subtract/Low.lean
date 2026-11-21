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

def borrowLowBytes : List UInt8 :=
  [0x4c, 0x89, 0xc8, 0x4c, 0x29, 0xf0, 0x49, 0xf7, 0xd1, 0x4c, 0x89, 0xf2, 0x4c, 0x21, 0xca, 0x4d, 0x9, 0xf1, 0x49, 0x21, 0xc1, 0x49, 0x9, 0xd1, 0x49, 0xc1, 0xe9, 0x3f, 0x4c, 0x89, 0xc, 0x24, 0x48, 0x89, 0xe2, 0x45, 0x31, 0xc9, 0x31, 0xd2, 0x48, 0x2b, 0x14, 0x24]

def borrowLowEffect (s : RamState) : Effect :=
  let a := (Operand.reg 9 : Operand 64).read s
  let b := (Operand.reg 14 : Operand 64).read s
  let r := a-b
  let q := (((~~~a ||| b) &&& r) ||| (b &&& ~~~a)) >>> 63
  { rip := 0x113f6e
    writes := [⟨(Operand.reg 0 : Operand 64), r⟩,
      ⟨(Operand.reg 9 : Operand 64), 0⟩,
      ⟨(Operand.reg 2 : Operand 64), -q⟩,
      ⟨(Operand.mem (stackPtr s) : Operand 64), q⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

set_option maxHeartbeats 1600000 in
theorem borrow_low_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (BorrowSlotPre 0x113f42)
      (codeRange 0x113f42 borrowLowBytes) (Effect.post borrowLowEffect) := by
  advance_begin (mov_r64_r64_effect_step 0x113f42 0x4c 0xc8 (by unfold RexWPrefix; decide +kernel) rfl)
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0x13f45 (by decide +kernel))
  advance_then (sub_r64_r64_effect_step 0x113f45 0x4c 0xf0 (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x113f42 borrowLowBytes 3 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13f48 (by decide +kernel))
  advance_then (not_r64_effect_step 0x113f48 0x49 0xd1 (by unfold RexWPrefix; decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113f42 borrowLowBytes 6 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13f4b (by decide +kernel))
  advance_then (mov_r64_r64_effect_step 0x113f4b 0x4c 0xf2 (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x113f42 borrowLowBytes 9 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13f4e (by decide +kernel))
  advance_then (and_r64_r64_effect_step 0x113f4e 0x4c 0xca (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x113f42 borrowLowBytes 12 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13f51 (by decide +kernel))
  advance_then (P256.Proofs.Common.Field.FieldNeg.Instructions.or_r64_r64_effect_step 0x113f51 0x4d 0xf1 (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x113f42 borrowLowBytes 15 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13f54 (by decide +kernel))
  advance_then (and_r64_r64_effect_step 0x113f54 0x49 0xc1 (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x113f42 borrowLowBytes 18 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13f57 (by decide +kernel))
  advance_then (P256.Proofs.Common.Field.FieldNeg.Instructions.or_r64_r64_effect_step 0x113f57 0x49 0xd1 (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x113f42 borrowLowBytes 21 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13f5a (by decide +kernel))
  advance_then (shr_r64_imm8_effect_step 0x113f5a 0x49 0xe9 63 (by unfold RexWPrefix; decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113f42 borrowLowBytes 24 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13f5e (by decide +kernel))
  advance_then (mov_m64_r64_effect_step 0x113f5e 0x4c (by unfold RexWPrefix; decide +kernel) 1 (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113f42 borrowLowBytes 28 4
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm [BitVec.add_zero]
      exact hP.writable
    · x86_norm [BitVec.add_zero]
      exact hP.apart 0x13f5e 4 (by decide +kernel)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [BitVec.add_zero]
      exact hP.apart 0x13f42 44 (by decide +kernel)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13f62 (by decide +kernel))
  advance_then (mov_r64_r64_effect_step 0x113f62 0x48 0xe2 (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x113f42 borrowLowBytes 32 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13f65 (by decide +kernel))
  advance_then (xor_r32_r32_rex_effect_step 0x113f65 0x45 0xc9 (by unfold RexNoWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x113f42 borrowLowBytes 35 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13f68 (by decide +kernel))
  advance_then (xor_r32_r32_effect_step 0x113f68 0xd2 rfl)
  case sub => exact codeRange_slice_subset 0x113f42 borrowLowBytes 38 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13f6a (by decide +kernel))
  advance_then (P256.Proofs.Common.Field.Instructions.sub_r64_m64_effect_step 0x113f6a 0x48 (by unfold RexWPrefix; decide +kernel) 2 (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113f42 borrowLowBytes 40 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [BitVec.add_zero]
      exact hP.writable.readable
    · apply Effect.Avoids.of_noMem
      simp [P256.Proofs.Common.Field.Instructions.subR64M64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13f6e (by decide +kernel))
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [borrowLowEffect, stackPtr, BitVec.xor_self, BitVec.zero_sub, BitVec.add_zero]
    all_goals try simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    all_goals (repeat' constructor)
  · x86_norm [borrowLowEffect, stackPtr, BitVec.xor_self, BitVec.zero_sub, BitVec.add_zero]
    all_goals try simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    all_goals (repeat' constructor)
  · intro i; cases i <;> x86_norm [borrowLowEffect, stackPtr, BitVec.xor_self, BitVec.zero_sub, BitVec.add_zero]
    all_goals try simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    all_goals (repeat' constructor)
  · x86_norm [borrowLowEffect, stackPtr, BitVec.xor_self, BitVec.zero_sub, BitVec.add_zero]
    all_goals try simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    all_goals (repeat' constructor)

theorem borrowLowBytes_code :
    P256.Spec.Program.Extracted.textBytes.toListFrom 0x13f42 44 = borrowLowBytes := by
  decide +kernel

end P256.Proofs.Field.Subtract
