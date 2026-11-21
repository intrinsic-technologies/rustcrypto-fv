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

open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Field.Add

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.SecretKeyFromBytes.Scalar (Limbs)
open P256.Proofs.Field.Montgomery.Reduction
open P256.Spec.Program.Routines
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def middleBytes : List UInt8 :=
  [0x49, 0x8d, 0x14, 0x8, 0x48, 0xb9, 0x1, 0x0, 0x0, 0x0, 0xff, 0xff, 0xff, 0xff, 0x48, 0x1, 0xca, 0x49, 0xf7, 0xd0, 0x49, 0x21, 0xd0, 0x49, 0xc1, 0xe8, 0x3f, 0x4c, 0x89, 0x4, 0x24, 0x49, 0x89, 0xe0, 0x45, 0x31, 0xc0, 0x4c, 0x2b, 0x4, 0x24, 0x49, 0xc1, 0xf8, 0x3f, 0x4d, 0x1, 0xd8, 0x49, 0xf7, 0xd3, 0x4d, 0x21, 0xc3, 0x49, 0xc1, 0xeb, 0x3f, 0x4c, 0x89, 0x1c, 0x24, 0x49, 0x89, 0xe3, 0x45, 0x31, 0xdb, 0x4c, 0x2b, 0x1c, 0x24, 0x49, 0xc1, 0xfb, 0x3f]

def middleEffect (s : RamState) : Effect :=
  let x := (Operand.reg 8 : Operand 64).read s
  let y := (Operand.reg 11 : Operand 64).read s
  let b := (Operand.reg 1 : Operand 64).read s
  let r1 := x + b + 0xffffffff00000001
  let b1 := (~~~x &&& r1) >>> 63
  let r2 := (-b1).sshiftRight 63 + y
  let b2 := (~~~y &&& r2) >>> 63
  { rip := 0x113ea2
    writes := [⟨(Operand.reg 2 : Operand 64), r1⟩,
      ⟨(Operand.reg 1 : Operand 64), 0xffffffff00000001⟩,
      ⟨(Operand.reg 8 : Operand 64), r2⟩,
      ⟨(Operand.reg 11 : Operand 64), (-b2).sshiftRight 63⟩,
      ⟨(Operand.mem (stackPtr s) : Operand 64), b2⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

def middleLowEffect (s : RamState) : Effect :=
  let x := (Operand.reg 8 : Operand 64).read s
  let b := (Operand.reg 1 : Operand 64).read s
  let r1 := x + b + 0xffffffff00000001
  let b1 := (~~~x &&& r1) >>> 63
  { rip := 0x113e83
    writes := [⟨(Operand.reg 2 : Operand 64), r1⟩,
      ⟨(Operand.reg 1 : Operand 64), 0xffffffff00000001⟩,
      ⟨(Operand.reg 8 : Operand 64), (-b1).sshiftRight 63⟩,
      ⟨(Operand.mem (stackPtr s) : Operand 64), b1⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

set_option maxHeartbeats 800000 in
theorem middle_low_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (BorrowSlotPre 0x113e56)
      (codeRange 0x113e56 middleBytes) (Effect.post middleLowEffect) := by
  advance_begin (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (lea_r64_effect_step 0x113e56 0x49 (by simp [RexWPrefix]) 2 (.sib 8 (some 1) 0 .none) (by decide +kernel) rfl rfl)))
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0x13e5a (by decide +kernel))
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (mov_r64_imm64_effect_step 0x113e5a 0x48 0xb9 (by simp [RexWPrefix]) (by decide) 0xffffffff00000001)))
  case sub => exact codeRange_slice_subset 0x113e56 middleBytes 4 10
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply P256.Proofs.Common.Instructions.Effect.Avoids.forgetFlags
      apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13e64 (by decide +kernel))
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (add_r64_r64_effect_step 0x113e64 0x48 0xca (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x113e56 middleBytes 14 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply P256.Proofs.Common.Instructions.Effect.Avoids.forgetFlags
      apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13e67 (by decide +kernel))
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (not_r64_effect_step 0x113e67 0x49 0xd0 (by simp [RexWPrefix]) rfl rfl)))
  case sub => exact codeRange_slice_subset 0x113e56 middleBytes 17 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply P256.Proofs.Common.Instructions.Effect.Avoids.forgetFlags
      apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13e6a (by decide +kernel))
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (and_r64_r64_effect_step 0x113e6a 0x49 0xd0 (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x113e56 middleBytes 20 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply P256.Proofs.Common.Instructions.Effect.Avoids.forgetFlags
      apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13e6d (by decide +kernel))
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (shr_r64_imm8_effect_step 0x113e6d 0x49 0xe8 63 (by simp [RexWPrefix]) rfl rfl)))
  case sub => exact codeRange_slice_subset 0x113e56 middleBytes 23 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply P256.Proofs.Common.Instructions.Effect.Avoids.forgetFlags
      apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13e71 (by decide +kernel))
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (mov_m64_r64_effect_step 0x113e71 0x4c (by simp [RexWPrefix]) 0 (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)))
  case sub => exact codeRange_slice_subset 0x113e56 middleBytes 27 4
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm [BitVec.add_zero]
      exact hP.writable
    · x86_norm [BitVec.add_zero]
      exact hP.apart 0x13e71 4 (by decide +kernel)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [BitVec.add_zero]
      exact hP.apart 0x13e56 76 (by decide +kernel)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13e75 (by decide +kernel))
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (mov_r64_r64_effect_step 0x113e75 0x49 0xe0 (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x113e56 middleBytes 31 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply P256.Proofs.Common.Instructions.Effect.Avoids.forgetFlags
      apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13e78 (by decide +kernel))
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (xor_r32_r32_rex_effect_step 0x113e78 0x45 0xc0 (by simp [RexNoWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x113e56 middleBytes 34 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply P256.Proofs.Common.Instructions.Effect.Avoids.forgetFlags
      apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13e7b (by decide +kernel))
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (P256.Proofs.Common.Field.Instructions.sub_r64_m64_effect_step 0x113e7b 0x4c (by simp [RexWPrefix]) 0 (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)))
  case sub => exact codeRange_slice_subset 0x113e56 middleBytes 37 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [BitVec.add_zero]
      exact hP.writable.readable
    · apply P256.Proofs.Common.Instructions.Effect.Avoids.forgetFlags
      apply Effect.Avoids.of_noMem
      simp [P256.Proofs.Common.Field.Instructions.subR64M64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13e7f (by decide +kernel))
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (P256.Proofs.Common.Instructions.sar_r64_imm8_effect_step 0x113e7f 0x49 0xf8 63 (by simp [RexWPrefix]) rfl rfl)))
  case sub => exact codeRange_slice_subset 0x113e56 middleBytes 41 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply P256.Proofs.Common.Instructions.Effect.Avoids.forgetFlags
      apply Effect.Avoids.of_noMem
      simp [P256.Proofs.Common.Instructions.sarR64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13e83 (by decide +kernel))
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [middleLowEffect]
  · x86_norm [middleLowEffect, stackPtr, BitVec.xor_self, BitVec.zero_sub,
      BitVec.add_zero, BitVec.setWidth_zero, BitVec.shiftLeft_zero]
    repeat' constructor
  · intro i
    cases i <;> x86_norm [middleLowEffect]
  · x86_norm [middleLowEffect, stackPtr, BitVec.add_zero]
    repeat' constructor

def middleHighEffect (s : RamState) : Effect :=
  let x := (Operand.reg 8 : Operand 64).read s
  let y := (Operand.reg 11 : Operand 64).read s
  let r2 := x + y
  let b2 := (~~~y &&& r2) >>> 63
  { rip := 0x113ea2
    writes := [⟨(Operand.reg 8 : Operand 64), r2⟩,
      ⟨(Operand.reg 11 : Operand 64), (-b2).sshiftRight 63⟩,
      ⟨(Operand.mem (stackPtr s) : Operand 64), b2⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

set_option maxHeartbeats 800000 in
theorem middle_high_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (BorrowSlotPre 0x113e83)
      (codeRange 0x113e56 middleBytes) (Effect.post middleHighEffect) := by
  advance_begin (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (add_r64_r64_effect_step 0x113e83 0x4d 0xd8 (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x113e56 middleBytes 45 3
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0x13e86 (by decide +kernel))
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (not_r64_effect_step 0x113e86 0x49 0xd3 (by simp [RexWPrefix]) rfl rfl)))
  case sub => exact codeRange_slice_subset 0x113e56 middleBytes 48 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply P256.Proofs.Common.Instructions.Effect.Avoids.forgetFlags
      apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13e89 (by decide +kernel))
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (and_r64_r64_effect_step 0x113e89 0x4d 0xc3 (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x113e56 middleBytes 51 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply P256.Proofs.Common.Instructions.Effect.Avoids.forgetFlags
      apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13e8c (by decide +kernel))
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (shr_r64_imm8_effect_step 0x113e8c 0x49 0xeb 63 (by simp [RexWPrefix]) rfl rfl)))
  case sub => exact codeRange_slice_subset 0x113e56 middleBytes 54 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply P256.Proofs.Common.Instructions.Effect.Avoids.forgetFlags
      apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13e90 (by decide +kernel))
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (mov_m64_r64_effect_step 0x113e90 0x4c (by simp [RexWPrefix]) 3 (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)))
  case sub => exact codeRange_slice_subset 0x113e56 middleBytes 58 4
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm [BitVec.add_zero]
      exact hP.writable
    · x86_norm [BitVec.add_zero]
      exact hP.apart 0x13e90 4 (by decide +kernel)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [BitVec.add_zero]
      exact hP.apart 0x13e56 76 (by decide +kernel)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13e94 (by decide +kernel))
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (mov_r64_r64_effect_step 0x113e94 0x49 0xe3 (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x113e56 middleBytes 62 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply P256.Proofs.Common.Instructions.Effect.Avoids.forgetFlags
      apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13e97 (by decide +kernel))
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (xor_r32_r32_rex_effect_step 0x113e97 0x45 0xdb (by simp [RexNoWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x113e56 middleBytes 65 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply P256.Proofs.Common.Instructions.Effect.Avoids.forgetFlags
      apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13e9a (by decide +kernel))
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (P256.Proofs.Common.Field.Instructions.sub_r64_m64_effect_step 0x113e9a 0x4c (by simp [RexWPrefix]) 3 (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)))
  case sub => exact codeRange_slice_subset 0x113e56 middleBytes 68 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [BitVec.add_zero]
      exact hP.writable.readable
    · apply P256.Proofs.Common.Instructions.Effect.Avoids.forgetFlags
      apply Effect.Avoids.of_noMem
      simp [P256.Proofs.Common.Field.Instructions.subR64M64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13e9e (by decide +kernel))
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (P256.Proofs.Common.Instructions.sar_r64_imm8_effect_step 0x113e9e 0x49 0xfb 63 (by simp [RexWPrefix]) rfl rfl)))
  case sub => exact codeRange_slice_subset 0x113e56 middleBytes 72 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply P256.Proofs.Common.Instructions.Effect.Avoids.forgetFlags
      apply Effect.Avoids.of_noMem
      simp [P256.Proofs.Common.Instructions.sarR64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13ea2 (by decide +kernel))
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [middleHighEffect]
  · x86_norm [middleHighEffect, stackPtr, BitVec.xor_self, BitVec.zero_sub,
      BitVec.add_zero, BitVec.setWidth_zero, BitVec.shiftLeft_zero]
    repeat' constructor
  · intro i
    cases i <;> x86_norm [middleHighEffect]
  · x86_norm [middleHighEffect, stackPtr, BitVec.add_zero]
    repeat' constructor

theorem middle_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (BorrowSlotPre 0x113e56)
      (codeRange 0x113e56 middleBytes) (Effect.post middleEffect) := by
  intro s ready code pre
  obtain ⟨n, t, run, rt, ct, et⟩ := middle_low_correct boundary hout s ready code pre
  have sp : stackPtr t = stackPtr s :=
    et.agrees.read (n := 64) (r := 4) (by simp [middleLowEffect, Effect.components])
  have next : BorrowSlotPre 0x113e83 t :=
    ⟨et.rip, by rw [sp]; exact pre.writable.of_holds et, by rw [sp]; exact pre.avoids⟩
  obtain ⟨m, u, run', ru, cu, eu⟩ := middle_high_correct boundary hout t rt ct next
  have r11 : (Operand.reg 11 : Operand 64).read t = (Operand.reg 11 : Operand 64).read s :=
    et.agrees.read (by simp [middleLowEffect, Effect.components])
  have r8 := et.writes.2.2.1
  change (middleHighEffect t).Holds t u at eu
  dsimp only [middleHighEffect] at eu
  rw [r8, r11, sp] at eu
  refine ⟨n+m, u, run.trans run', ru, cu, eu.rip, ?_,
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩, ?_⟩
  · dsimp only [middleEffect, Write.AllHold]
    refine ⟨?_, ?_, eu.writes.1, eu.writes.2.1, eu.writes.2.2⟩
    · exact (eu.agrees.read (n := 64) (r := 2) (by simp [Effect.components])).trans et.writes.1
    · exact (eu.agrees.read (n := 64) (r := 1) (by simp [Effect.components])).trans et.writes.2.1
  · apply (et.agrees.trans eu.agrees).mono
    simp [middleEffect, middleLowEffect, Effect.components]

theorem middleBytes_code :
    P256.Spec.Program.Extracted.textBytes.toListFrom 0x13e56 76 = middleBytes := by
  decide +kernel

end P256.Proofs.Field.Add
