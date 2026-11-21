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
import P256.Proofs.Field.Add.Arithmetic

set_option autoImplicit false

open P256.Proofs.Common.Instructions.AddByte (addR8Imm8Effect add_ff_carry add_sil_ff_effect_step)
open P256.Proofs.Common.Instructions.Carry (adcR64Imm8Effect_components adc_r64_imm8_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Field.Add

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.SecretKeyFromBytes.Scalar (Limbs)
open P256.Proofs.Field.Montgomery.Reduction
open P256.Spec.Program.Routines
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def upperBytes : List UInt8 :=
  [0x4b, 0x8d, 0x1c, 0x19, 0x41, 0xbb, 0xff, 0xff, 0xff, 0xff, 0x49, 0x1, 0xdb, 0x49, 0xf7, 0xd1, 0x4d, 0x9, 0xd9, 0x49, 0xc1, 0xe9, 0x3f, 0x4c, 0x89, 0xc, 0x24, 0x49, 0x89, 0xe1, 0x4c, 0x2b, 0x14, 0x24, 0x49, 0xc1, 0xfa, 0x3f, 0x40, 0x80, 0xc6, 0xff, 0x49, 0x83, 0xd2, 0x0, 0x49, 0xc1, 0xea, 0x3f, 0x4c, 0x89, 0x14, 0x24, 0x48, 0x89, 0xe6, 0x48, 0x8b, 0x34, 0x24]

def upperEffect (s : RamState) : Effect :=
  let x := (Operand.reg 9 : Operand 64).read s
  let b := (Operand.reg 11 : Operand 64).read s
  let r := x + b + 0xffffffff
  let borrow := (~~~x ||| r) >>> 63
  let carryIn := decide ((Operand.reg 6 : Operand 8).read s ≠ 0)
  let q := (((Operand.reg 10 : Operand 64).read s - borrow).sshiftRight 63 +
    BitVec.ofNat 64 carryIn.toNat) >>> 63
  { rip := 0x113edf
    writes := [⟨(Operand.reg 3 : Operand 64), x + b⟩,
      ⟨(Operand.reg 11 : Operand 64), r⟩,
      ⟨(Operand.reg 9 : Operand 64), stackPtr s⟩,
      ⟨(Operand.reg 10 : Operand 64), q⟩,
      ⟨(Operand.reg 6 : Operand 64), q⟩,
      ⟨(Operand.mem (stackPtr s) : Operand 64), q⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

set_option maxHeartbeats 1600000 in
theorem upper_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (BorrowSlotPre 0x113ea2)
      (codeRange 0x113ea2 upperBytes) (Effect.post upperEffect) := by
  advance_begin (lea_r64_effect_step 0x113ea2 0x4b (by simp [RexWPrefix]) 3 (.sib 9 (some 11) 0 .none) (by decide +kernel) rfl rfl)
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0x13ea6 (by decide +kernel))
  advance_then (mov_r32_imm32_rex_effect_step 0x113ea6 0x41 0xbb (by simp [RexNoWPrefix]) (by decide) 0xffffffff)
  case sub => exact codeRange_slice_subset 0x113ea2 upperBytes 4 6
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13eac (by decide +kernel))
  advance_then (add_r64_r64_effect_step 0x113eac 0x49 0xdb (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x113ea2 upperBytes 10 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13eaf (by decide +kernel))
  advance_then (not_r64_effect_step 0x113eaf 0x49 0xd1 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113ea2 upperBytes 13 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13eb2 (by decide +kernel))
  advance_then (P256.Proofs.Common.Field.FieldNeg.Instructions.or_r64_r64_effect_step 0x113eb2 0x4d 0xd9 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x113ea2 upperBytes 16 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13eb5 (by decide +kernel))
  advance_then (shr_r64_imm8_effect_step 0x113eb5 0x49 0xe9 63 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113ea2 upperBytes 19 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13eb9 (by decide +kernel))
  advance_then (mov_m64_r64_effect_step 0x113eb9 0x4c (by simp [RexWPrefix]) 1 (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113ea2 upperBytes 23 4
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm [BitVec.add_zero]
      exact hP.writable
    · x86_norm [BitVec.add_zero]
      exact hP.apart 0x13eb9 4 (by decide +kernel)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [BitVec.add_zero]
      exact hP.apart 0x13ea2 61 (by decide +kernel)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13ebd (by decide +kernel))
  advance_then (mov_r64_r64_effect_step 0x113ebd 0x49 0xe1 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x113ea2 upperBytes 27 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13ec0 (by decide +kernel))
  advance_then (P256.Proofs.Common.Field.Instructions.sub_r64_m64_effect_step 0x113ec0 0x4c (by simp [RexWPrefix]) 2 (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113ea2 upperBytes 30 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [BitVec.add_zero]
      exact hP.writable.readable
    · apply Effect.Avoids.of_noMem
      simp [P256.Proofs.Common.Field.Instructions.subR64M64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13ec4 (by decide +kernel))
  advance_then (P256.Proofs.Common.Instructions.sar_r64_imm8_effect_step 0x113ec4 0x49 0xfa 63 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113ea2 upperBytes 34 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [P256.Proofs.Common.Instructions.sarR64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13ec8 (by decide +kernel))
  advance_then (add_sil_ff_effect_step 0x113ec8)
  case sub => exact codeRange_slice_subset 0x113ea2 upperBytes 38 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [addR8Imm8Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13ecc (by decide +kernel))
  advance_then_on [StatusFlag.CF] using (adc_r64_imm8_effect_step 0x113ecc 0x49 0xd2 0 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113ea2 upperBytes 42 4
  case mid =>
    intro s t hP hH hO hF
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [adcR64Imm8Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13ed0 (by decide +kernel))
  advance_then (shr_r64_imm8_effect_step 0x113ed0 0x49 0xea 63 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113ea2 upperBytes 46 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13ed4 (by decide +kernel))
  advance_then (mov_m64_r64_effect_step 0x113ed4 0x4c (by simp [RexWPrefix]) 2 (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113ea2 upperBytes 50 4
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm [BitVec.add_zero]
      exact hP.writable
    · x86_norm [BitVec.add_zero]
      exact hP.apart 0x13ed4 4 (by decide +kernel)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [BitVec.add_zero]
      exact hP.apart 0x13ea2 61 (by decide +kernel)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13ed8 (by decide +kernel))
  advance_then (mov_r64_r64_effect_step 0x113ed8 0x48 0xe6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x113ea2 upperBytes 54 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13edb (by decide +kernel))
  advance_then (mov_r64_m64_effect_step 0x113edb 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113ea2 upperBytes 57 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [BitVec.add_zero]
      exact hP.writable.readable
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13edf (by decide +kernel))
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [upperEffect]
  · x86_norm [upperEffect, stackPtr, adcSpec_ofBool, adc,
      BitVec.add_zero]
    have hc : (addSpec ((Operand.reg 6#5 : Operand 8).read s) 255#8).2.CF =
        decide ((Operand.reg 6#5 : Operand 8).read s ≠ 0#8) :=
      add_ff_carry _
    simp only [BitVec.shiftLeft_zero, hc,
      BitVec.add_comm (4294967295#64), BitVec.add_assoc,
      ← Operand.read_reg64, or_self]
    repeat' constructor
  · intro i
    cases i <;> x86_norm [upperEffect]
  · x86_norm [upperEffect, stackPtr, BitVec.add_zero]
    repeat' constructor

theorem upperBytes_code :
    P256.Spec.Program.Extracted.textBytes.toListFrom 0x13ea2 61 = upperBytes := by
  decide +kernel

end P256.Proofs.Field.Add
