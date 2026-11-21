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

open P256.Proofs.Field.Montgomery.Reduction (BorrowSlotPre)
open P256.Proofs.Common.Instructions.Setb (setccR8Effect_avoids setcc_r8_rex_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Field.Add

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.SecretKeyFromBytes.Scalar (Limbs)
open P256.Proofs.Field.Montgomery.Reduction
open P256.Spec.Program.Routines
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def lowBytes : List UInt8 :=
  [0x48,0x8d,0x41,1,0x48,0xf7,0xd1,0x40,0x0f,0x92,0xc6,0x48,0x09,0xc1,
   0x48,0xc1,0xe9,0x3f,0x48,0x89,0x0c,0x24,0x48,0x89,0xe1,
   0x45,0x31,0xd2,0x31,0xc9,0x48,0x2b,0x0c,0x24,0x48,0xc1,0xf9,0x3f]

def lowEffect (s : RamState) : Effect :=
  let a := (Operand.reg 1 : Operand 64).read s
  let r := a + 1
  let b := (~~~a ||| r) >>> 63
  { rip := 0x113e56
    writes := [⟨(Operand.reg 0 : Operand 64), r⟩,
      ⟨(Operand.reg 1 : Operand 64), (-b).sshiftRight 63⟩,
      ⟨(Operand.reg 6 : Operand 64), mergeGPR 8
        (if (StatusFlags.ofRFLAGS s.RFLAGS).CF then 1#8 else 0#8)
        ((Operand.reg 6 : Operand 64).read s)⟩,
      ⟨(Operand.reg 10 : Operand 64), 0⟩,
      ⟨(Operand.mem (stackPtr s) : Operand 64), b⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

set_option maxHeartbeats 800000 in
theorem low_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (BorrowSlotPre 0x113e30) (codeRange 0x113e30 lowBytes)
      (Effect.post lowEffect) := by
  advance_begin (lea_r64_effect_step 0x113e30 0x48 (by simp [RexWPrefix])
    0 (.base 1 (.d8 1)) (by decide +kernel) rfl rfl)
  case next =>
    intro s hP
    exact boundary_ne_program hout (inProgram_of_textOffset 0x13e34 (by decide))
  advance_then (not_r64_effect_step 0x113e34 0x48 0xd1
    (by simp [RexWPrefix]) (by decide) (by decide))
  case sub => exact codeRange_slice_subset 0x113e30 lowBytes 4 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13e37 (by decide))
  advance_then_on [StatusFlag.CF] using (setcc_r8_rex_effect_step 0x113e37 0x40 0x92 0xc6
    (by simp [RexPrefix]) (.inl rfl) (by decide))
  case sub => exact codeRange_slice_subset 0x113e30 lowBytes 7 4
  case mid =>
    intro s t hP hH hO hF
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · exact setccR8Effect_avoids _ _ _ _ _ _
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13e3b (by decide))
  advance_then (P256.Proofs.Common.Field.FieldNeg.Instructions.or_r64_r64_effect_step 0x113e3b 0x48 0xc1
    (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x113e30 lowBytes 11 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13e3e (by decide))
  advance_then (shr_r64_imm8_effect_step 0x113e3e 0x48 0xe9 63
    (by simp [RexWPrefix]) (by decide) (by decide))
  case sub => exact codeRange_slice_subset 0x113e30 lowBytes 14 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13e42 (by decide))
  advance_then (mov_m64_r64_effect_step 0x113e42 0x48 (by simp [RexWPrefix])
    1 (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113e30 lowBytes 18 4
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      change MemWritable s (stackPtr s + 0#64) 8
      rw [BitVec.add_zero]
      exact hP.writable
    · x86_norm
      change RangeApart (stackPtr s + 0#64) 8 _ 4
      rw [BitVec.add_zero]
      exact hP.apart 0x13e42 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      change RangeApart (stackPtr s + 0#64) 8 _ 38
      rw [BitVec.add_zero]
      exact hP.apart 0x13e30 38 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13e46 (by decide))
  advance_then (mov_r64_r64_effect_step 0x113e46 0x48 0xe1
    (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x113e30 lowBytes 22 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13e49 (by decide))
  advance_then (xor_r32_r32_rex_effect_step 0x113e49 0x45 0xd2
    (by simp [RexNoWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x113e30 lowBytes 25 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13e4c (by decide))
  advance_then (xor_r32_r32_effect_step 0x113e4c 0xc9 (by decide))
  case sub => exact codeRange_slice_subset 0x113e30 lowBytes 28 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13e4e (by decide))
  advance_then (P256.Proofs.Common.Field.Instructions.sub_r64_m64_effect_step 0x113e4e 0x48
    (by simp [RexWPrefix]) 1 (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113e30 lowBytes 30 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      change MemReadable s (stackPtr s + 0#64) 8
      rw [BitVec.add_zero]
      exact hP.writable.readable
    · apply Effect.Avoids.of_noMem
      simp [P256.Proofs.Common.Field.Instructions.subR64M64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13e52 (by decide))
  advance_then (P256.Proofs.Common.Instructions.sar_r64_imm8_effect_step 0x113e52 0x48 0xf9 63
    (by simp [RexWPrefix]) (by decide) (by decide))
  case sub => exact codeRange_slice_subset 0x113e30 lowBytes 34 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [P256.Proofs.Common.Instructions.sarR64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13e56 (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [lowEffect]
  · x86_norm [lowEffect]
    simp [gprNumber, rexB, rexR, modrmRm, modrmReg, shiftCount,
      Operand.read_reg64]
  · intro i
    cases i <;> exact .inl rfl
  · x86_norm [lowEffect]
    change (stackPtr s + 0#64) = stackPtr s
    exact BitVec.add_zero _

theorem lowBytes_code :
    P256.Spec.Program.Extracted.textBytes.toListFrom 0x13e30 38 = lowBytes := by
  decide +kernel

end P256.Proofs.Field.Add
