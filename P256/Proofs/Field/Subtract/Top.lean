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

def borrowTopBytes : List UInt8 :=
  [0x4c, 0x2b, 0x14, 0x24, 0x49, 0x89, 0xcb, 0x49, 0x29, 0xf3, 0x49, 0xc1, 0xfa, 0x3f, 0x4d, 0x1, 0xda, 0x48, 0xf7, 0xd1, 0x49, 0x89, 0xf3, 0x49, 0x21, 0xcb, 0x48, 0x9, 0xf1, 0x4c, 0x21, 0xd1, 0x4c, 0x9, 0xd9, 0x48, 0xc1, 0xe9, 0x3f, 0x48, 0x89, 0xc, 0x24, 0x48, 0x89, 0xe1, 0x4c, 0x2b, 0xc, 0x24, 0x49, 0xc1, 0xe9, 0x3f, 0x4c, 0x89, 0xc, 0x24, 0x48, 0x8b, 0xc, 0x24]

def borrowTopEffect (s : RamState) : Effect :=
  let a := (Operand.reg 1 : Operand 64).read s
  let b := (Operand.reg 6 : Operand 64).read s
  let r := ((Operand.reg 10 : Operand 64).read s - (Operand.mem (stackPtr s) : Operand 64).read s).sshiftRight 63 + (a-b)
  let q := (((~~~a ||| b) &&& r) ||| (b &&& ~~~a)) >>> 63
  let mask := ((Operand.reg 9 : Operand 64).read s - q) >>> 63
  { rip := 0x11400a
    writes := [⟨(Operand.reg 11 : Operand 64), b &&& ~~~a⟩,
      ⟨(Operand.reg 10 : Operand 64), r⟩,
      ⟨(Operand.reg 9 : Operand 64), mask⟩,
      ⟨(Operand.reg 1 : Operand 64), mask⟩,
      ⟨(Operand.mem (stackPtr s) : Operand 64), mask⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

set_option maxHeartbeats 1600000 in
theorem borrow_top_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (BorrowSlotPre 0x113fcc)
      (codeRange 0x113fcc borrowTopBytes) (Effect.post borrowTopEffect) := by
  advance_begin (P256.Proofs.Common.Field.Instructions.sub_r64_m64_effect_step 0x113fcc 0x4c (by unfold RexWPrefix; decide +kernel) 2 (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    refine ⟨h.rip, ?_⟩
    change MemReadable s (stackPtr s + 0#64) 8
    simpa only [BitVec.add_zero] using h.writable.readable
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0x13fd0 (by decide +kernel))
  advance_then (mov_r64_r64_effect_step 0x113fd0 0x49 0xcb (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x113fcc borrowTopBytes 4 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13fd3 (by decide +kernel))
  advance_then (sub_r64_r64_effect_step 0x113fd3 0x49 0xf3 (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x113fcc borrowTopBytes 7 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13fd6 (by decide +kernel))
  advance_then (P256.Proofs.Common.Instructions.sar_r64_imm8_effect_step 0x113fd6 0x49 0xfa 63 (by unfold RexWPrefix; decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113fcc borrowTopBytes 10 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [P256.Proofs.Common.Instructions.sarR64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13fda (by decide +kernel))
  advance_then (add_r64_r64_effect_step 0x113fda 0x4d 0xda (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x113fcc borrowTopBytes 14 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13fdd (by decide +kernel))
  advance_then (not_r64_effect_step 0x113fdd 0x48 0xd1 (by unfold RexWPrefix; decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113fcc borrowTopBytes 17 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13fe0 (by decide +kernel))
  advance_then (mov_r64_r64_effect_step 0x113fe0 0x49 0xf3 (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x113fcc borrowTopBytes 20 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13fe3 (by decide +kernel))
  advance_then (and_r64_r64_effect_step 0x113fe3 0x49 0xcb (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x113fcc borrowTopBytes 23 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13fe6 (by decide +kernel))
  advance_then (P256.Proofs.Common.Field.FieldNeg.Instructions.or_r64_r64_effect_step 0x113fe6 0x48 0xf1 (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x113fcc borrowTopBytes 26 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13fe9 (by decide +kernel))
  advance_then (and_r64_r64_effect_step 0x113fe9 0x4c 0xd1 (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x113fcc borrowTopBytes 29 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13fec (by decide +kernel))
  advance_then (P256.Proofs.Common.Field.FieldNeg.Instructions.or_r64_r64_effect_step 0x113fec 0x4c 0xd9 (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x113fcc borrowTopBytes 32 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13fef (by decide +kernel))
  advance_then (shr_r64_imm8_effect_step 0x113fef 0x48 0xe9 63 (by unfold RexWPrefix; decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113fcc borrowTopBytes 35 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13ff3 (by decide +kernel))
  advance_then (mov_m64_r64_effect_step 0x113ff3 0x48 (by unfold RexWPrefix; decide +kernel) 1 (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113fcc borrowTopBytes 39 4
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm [BitVec.add_zero]
      exact hP.writable
    · x86_norm [BitVec.add_zero]
      exact hP.apart 0x13ff3 4 (by decide +kernel)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [BitVec.add_zero]
      exact hP.apart 0x13fcc 62 (by decide +kernel)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13ff7 (by decide +kernel))
  advance_then (mov_r64_r64_effect_step 0x113ff7 0x48 0xe1 (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x113fcc borrowTopBytes 43 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13ffa (by decide +kernel))
  advance_then (P256.Proofs.Common.Field.Instructions.sub_r64_m64_effect_step 0x113ffa 0x4c (by unfold RexWPrefix; decide +kernel) 1 (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113fcc borrowTopBytes 46 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [BitVec.add_zero]
      exact hP.writable.readable
    · apply Effect.Avoids.of_noMem
      simp [P256.Proofs.Common.Field.Instructions.subR64M64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13ffe (by decide +kernel))
  advance_then (shr_r64_imm8_effect_step 0x113ffe 0x49 0xe9 63 (by unfold RexWPrefix; decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113fcc borrowTopBytes 50 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x14002 (by decide +kernel))
  advance_then (mov_m64_r64_effect_step 0x114002 0x4c (by unfold RexWPrefix; decide +kernel) 1 (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113fcc borrowTopBytes 54 4
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm [BitVec.add_zero]
      exact hP.writable
    · x86_norm [BitVec.add_zero]
      exact hP.apart 0x14002 4 (by decide +kernel)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [BitVec.add_zero]
      exact hP.apart 0x13fcc 62 (by decide +kernel)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x14006 (by decide +kernel))
  advance_then (mov_r64_m64_effect_step 0x114006 0x48 (by unfold RexWPrefix; decide +kernel) 1 (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113fcc borrowTopBytes 58 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [BitVec.add_zero]
      exact hP.writable.readable
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1400a (by decide +kernel))
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [borrowTopEffect, stackPtr, BitVec.xor_self, BitVec.zero_sub, BitVec.add_zero]
    all_goals try simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    all_goals (repeat' constructor)
  · x86_norm [borrowTopEffect, stackPtr, BitVec.xor_self, BitVec.zero_sub, BitVec.add_zero]
    all_goals try simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    all_goals (repeat' constructor)
  · intro i; cases i <;> x86_norm [borrowTopEffect, stackPtr, BitVec.xor_self, BitVec.zero_sub, BitVec.add_zero]
    all_goals try simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    all_goals (repeat' constructor)
  · x86_norm [borrowTopEffect, stackPtr, BitVec.xor_self, BitVec.zero_sub, BitVec.add_zero]
    all_goals try simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    all_goals (repeat' constructor)

theorem borrowTopBytes_code :
    P256.Spec.Program.Extracted.textBytes.toListFrom 0x13fcc 62 = borrowTopBytes := by
  decide +kernel

end P256.Proofs.Field.Subtract
