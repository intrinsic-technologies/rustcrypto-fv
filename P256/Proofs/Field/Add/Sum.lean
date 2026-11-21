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

open P256.Proofs.Common.Instructions (addR64M64Effect_components add_r64_m64_effect_step)
open P256.Proofs.Common.Instructions.Carry (adcR64M64Effect_components adc_r64_m64_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Field.Add

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.SecretKeyFromBytes.Scalar (Limbs)
open P256.Proofs.Field.Montgomery.Reduction
open P256.Spec.Program.Routines
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure SumPre (s : RamState) : Prop where
  rip : s.RIP = 0x113e12
  left : ∀ i ∈ [0, 8, 16, 24], MemReadable s ((Operand.reg 6 : Operand 64).read s + i) 8
  right : ∀ i ∈ [0, 8, 16, 24], MemReadable s ((Operand.reg 2 : Operand 64).read s + i) 8

def sumBytes : List UInt8 :=
  [0x48, 0x8b, 0x0a, 0x48, 0x03, 0x0e, 0x4c, 0x8b, 0x42, 8,
   0x4c, 0x13, 0x46, 8, 0x4c, 0x8b, 0x5a, 16, 0x4c, 0x13, 0x5e, 16,
   0x4c, 0x8b, 0x4a, 24, 0x4c, 0x13, 0x4e, 24]

def sumEffect (s : RamState) : Effect :=
  let result := addRaw (readLimbs s ((Operand.reg 2 : Operand 64).read s)) (readLimbs s ((Operand.reg 6 : Operand 64).read s))
  { rip := 0x113e30
    writes := [⟨(Operand.reg 1 : Operand 64), result.1.l0⟩,
      ⟨(Operand.reg 8 : Operand 64), result.1.l1⟩,
      ⟨(Operand.reg 11 : Operand 64), result.1.l2⟩,
      ⟨(Operand.reg 9 : Operand 64), result.1.l3⟩]
    flags := some ⟨some result.2, none, none, none, none, none⟩ }

set_option maxHeartbeats 800000 in
theorem sum_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary SumPre (codeRange 0x113e12 sumBytes) (Effect.post sumEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x113e12 0x48
    (by simp [RexWPrefix]) 1 (.base 2 .none) (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    exact ⟨h.rip, h.right 0 (by simp)⟩
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0x13e15 (by decide))
  advance_then (add_r64_m64_effect_step 0x113e15 0x48
    (by simp [RexWPrefix]) 1 (.base 6 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113e12 sumBytes 3 3
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.left 0 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [addR64M64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13e18 (by decide))
  advance_then (mov_r64_m64_effect_step 0x113e18 0x4c
    (by simp [RexWPrefix]) 0 (.base 2 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113e12 sumBytes 6 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.right 8 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13e1c (by decide))
  advance_then_on [StatusFlag.CF] using (adc_r64_m64_effect_step 0x113e1c 0x4c
    (by simp [RexWPrefix]) 0 (.base 6 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113e12 sumBytes 10 4
  case mid =>
    intro s t hP hH hO hF
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.left 8 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [adcR64M64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13e20 (by decide))
  advance_then (mov_r64_m64_effect_step 0x113e20 0x4c
    (by simp [RexWPrefix]) 3 (.base 2 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113e12 sumBytes 14 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.right 16 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13e24 (by decide))
  advance_then_on [StatusFlag.CF] using (adc_r64_m64_effect_step 0x113e24 0x4c
    (by simp [RexWPrefix]) 3 (.base 6 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113e12 sumBytes 18 4
  case mid =>
    intro s t hP hH hO hF
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.left 16 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [adcR64M64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13e28 (by decide))
  advance_then (mov_r64_m64_effect_step 0x113e28 0x4c
    (by simp [RexWPrefix]) 1 (.base 2 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113e12 sumBytes 22 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.right 24 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13e2c (by decide))
  advance_then_on [StatusFlag.CF] using (adc_r64_m64_effect_step 0x113e2c 0x4c
    (by simp [RexWPrefix]) 1 (.base 6 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113e12 sumBytes 26 4
  case mid =>
    intro s t hP hH hO hF
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.left 24 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [adcR64M64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13e30 (by decide))
  advance_finish [sumEffect, addRaw, readLimbs, adcSpec_ofBool,
    adcSpec_cf_ofBool, addSpec_cf_carry, adc,
    Bool.toNat_false, Nat.zero_mod, BitVec.add_zero]

theorem sumBytes_code :
    P256.Spec.Program.Extracted.textBytes.toListFrom 0x13e12 30 = sumBytes := by
  decide +kernel

end P256.Proofs.Field.Add
