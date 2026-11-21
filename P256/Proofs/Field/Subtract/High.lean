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

def borrowHighBytes : List UInt8 :=
  [0x4c, 0x2b, 0x4, 0x24, 0x4c, 0x89, 0xd3, 0x4c, 0x29, 0xdb, 0x49, 0xc1, 0xf8, 0x3f, 0x49, 0x1, 0xd8, 0x49, 0xf7, 0xd2, 0x4c, 0x89, 0xdb, 0x4c, 0x21, 0xd3, 0x4d, 0x9, 0xda, 0x4d, 0x21, 0xc2, 0x49, 0x9, 0xda, 0x49, 0xc1, 0xea, 0x3f, 0x4c, 0x89, 0x14, 0x24, 0x49, 0x89, 0xe2, 0x45, 0x31, 0xd2]

def borrowHighEffect (s : RamState) : Effect :=
  let a := (Operand.reg 10 : Operand 64).read s
  let b := (Operand.reg 11 : Operand 64).read s
  let r := ((Operand.reg 8 : Operand 64).read s - (Operand.mem (stackPtr s) : Operand 64).read s).sshiftRight 63 + (a-b)
  let q := (((~~~a ||| b) &&& r) ||| (b &&& ~~~a)) >>> 63
  { rip := 0x113fcc
    writes := [⟨(Operand.reg 3 : Operand 64), b &&& ~~~a⟩,
      ⟨(Operand.reg 8 : Operand 64), r⟩,
      ⟨(Operand.reg 10 : Operand 64), 0⟩,
      ⟨(Operand.mem (stackPtr s) : Operand 64), q⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

set_option maxHeartbeats 1600000 in
theorem borrow_high_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (BorrowSlotPre 0x113f9b)
      (codeRange 0x113f9b borrowHighBytes) (Effect.post borrowHighEffect) := by
  advance_begin (P256.Proofs.Common.Field.Instructions.sub_r64_m64_effect_step 0x113f9b 0x4c (by unfold RexWPrefix; decide +kernel) 0 (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    refine ⟨h.rip, ?_⟩
    change MemReadable s (stackPtr s + 0#64) 8
    simpa only [BitVec.add_zero] using h.writable.readable
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0x13f9f (by decide +kernel))
  advance_then (mov_r64_r64_effect_step 0x113f9f 0x4c 0xd3 (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x113f9b borrowHighBytes 4 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13fa2 (by decide +kernel))
  advance_then (sub_r64_r64_effect_step 0x113fa2 0x4c 0xdb (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x113f9b borrowHighBytes 7 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13fa5 (by decide +kernel))
  advance_then (P256.Proofs.Common.Instructions.sar_r64_imm8_effect_step 0x113fa5 0x49 0xf8 63 (by unfold RexWPrefix; decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113f9b borrowHighBytes 10 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [P256.Proofs.Common.Instructions.sarR64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13fa9 (by decide +kernel))
  advance_then (add_r64_r64_effect_step 0x113fa9 0x49 0xd8 (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x113f9b borrowHighBytes 14 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13fac (by decide +kernel))
  advance_then (not_r64_effect_step 0x113fac 0x49 0xd2 (by unfold RexWPrefix; decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113f9b borrowHighBytes 17 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13faf (by decide +kernel))
  advance_then (mov_r64_r64_effect_step 0x113faf 0x4c 0xdb (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x113f9b borrowHighBytes 20 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13fb2 (by decide +kernel))
  advance_then (and_r64_r64_effect_step 0x113fb2 0x4c 0xd3 (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x113f9b borrowHighBytes 23 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13fb5 (by decide +kernel))
  advance_then (P256.Proofs.Common.Field.FieldNeg.Instructions.or_r64_r64_effect_step 0x113fb5 0x4d 0xda (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x113f9b borrowHighBytes 26 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13fb8 (by decide +kernel))
  advance_then (and_r64_r64_effect_step 0x113fb8 0x4d 0xc2 (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x113f9b borrowHighBytes 29 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13fbb (by decide +kernel))
  advance_then (P256.Proofs.Common.Field.FieldNeg.Instructions.or_r64_r64_effect_step 0x113fbb 0x49 0xda (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x113f9b borrowHighBytes 32 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13fbe (by decide +kernel))
  advance_then (shr_r64_imm8_effect_step 0x113fbe 0x49 0xea 63 (by unfold RexWPrefix; decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113f9b borrowHighBytes 35 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13fc2 (by decide +kernel))
  advance_then (mov_m64_r64_effect_step 0x113fc2 0x4c (by unfold RexWPrefix; decide +kernel) 2 (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113f9b borrowHighBytes 39 4
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm [BitVec.add_zero]
      exact hP.writable
    · x86_norm [BitVec.add_zero]
      exact hP.apart 0x13fc2 4 (by decide +kernel)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [BitVec.add_zero]
      exact hP.apart 0x13f9b 49 (by decide +kernel)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13fc6 (by decide +kernel))
  advance_then (mov_r64_r64_effect_step 0x113fc6 0x49 0xe2 (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x113f9b borrowHighBytes 43 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13fc9 (by decide +kernel))
  advance_then (xor_r32_r32_rex_effect_step 0x113fc9 0x45 0xd2 (by unfold RexNoWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x113f9b borrowHighBytes 46 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13fcc (by decide +kernel))
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [borrowHighEffect, stackPtr, BitVec.xor_self, BitVec.zero_sub, BitVec.add_zero]
    all_goals try simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    all_goals (repeat' constructor)
  · x86_norm [borrowHighEffect, stackPtr, BitVec.xor_self, BitVec.zero_sub, BitVec.add_zero]
    all_goals try simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    all_goals (repeat' constructor)
  · intro i; cases i <;> x86_norm [borrowHighEffect, stackPtr, BitVec.xor_self, BitVec.zero_sub, BitVec.add_zero]
    all_goals try simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    all_goals (repeat' constructor)
  · x86_norm [borrowHighEffect, stackPtr, BitVec.xor_self, BitVec.zero_sub, BitVec.add_zero]
    all_goals try simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    all_goals (repeat' constructor)

theorem borrowHighBytes_code :
    P256.Spec.Program.Extracted.textBytes.toListFrom 0x13f9b 49 = borrowHighBytes := by
  decide +kernel

end P256.Proofs.Field.Subtract
