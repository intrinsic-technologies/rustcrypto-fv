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

structure LoadLimbsPre (s : RamState) : Prop where
  rip : s.RIP = 0x113f24
  left : ∀ i ∈ [0, 8, 16, 24], MemReadable s ((Operand.reg 6 : Operand 64).read s + i) 8
  right : ∀ i ∈ [0, 8, 16, 24], MemReadable s ((Operand.reg 2 : Operand 64).read s + i) 8

def loadLimbsBytes : List UInt8 :=
  [0x4c, 0x8b, 0xe, 0x4c, 0x8b, 0x46, 0x8, 0x4c, 0x8b, 0x56, 0x10, 0x48, 0x8b, 0x4e, 0x18, 0x4c, 0x8b, 0x32, 0x48, 0x8b, 0x5a, 0x8, 0x4c, 0x8b, 0x5a, 0x10, 0x48, 0x8b, 0x72, 0x18]

def loadLimbsEffect (s : RamState) : Effect :=
  { rip := 0x113f42
    writes := [
      ⟨(Operand.reg 9 : Operand 64),
        (Operand.mem ((Operand.reg 6 : Operand 64).read s + 0) : Operand 64).read s⟩,
      ⟨(Operand.reg 8 : Operand 64),
        (Operand.mem ((Operand.reg 6 : Operand 64).read s + 8) : Operand 64).read s⟩,
      ⟨(Operand.reg 10 : Operand 64),
        (Operand.mem ((Operand.reg 6 : Operand 64).read s + 16) : Operand 64).read s⟩,
      ⟨(Operand.reg 1 : Operand 64),
        (Operand.mem ((Operand.reg 6 : Operand 64).read s + 24) : Operand 64).read s⟩,
      ⟨(Operand.reg 14 : Operand 64),
        (Operand.mem ((Operand.reg 2 : Operand 64).read s + 0) : Operand 64).read s⟩,
      ⟨(Operand.reg 3 : Operand 64),
        (Operand.mem ((Operand.reg 2 : Operand 64).read s + 8) : Operand 64).read s⟩,
      ⟨(Operand.reg 11 : Operand 64),
        (Operand.mem ((Operand.reg 2 : Operand 64).read s + 16) : Operand 64).read s⟩,
      ⟨(Operand.reg 6 : Operand 64),
        (Operand.mem ((Operand.reg 2 : Operand 64).read s + 24) : Operand 64).read s⟩] }

set_option maxHeartbeats 800000 in
theorem load_limbs_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary LoadLimbsPre (codeRange 0x113f24 loadLimbsBytes)
      (Effect.post loadLimbsEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x113f24 0x4c
    (by simp [RexWPrefix]) 1 (.base 6 .none) (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    refine ⟨h.rip, ?_⟩
    exact h.left 0 (by simp)
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0x13f27 (by decide))
  advance_then (mov_r64_m64_effect_step 0x113f27 0x4c
    (by simp [RexWPrefix]) 0 (.base 6 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113f24 loadLimbsBytes 3 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.left 8 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13f2b (by decide))
  advance_then (mov_r64_m64_effect_step 0x113f2b 0x4c
    (by simp [RexWPrefix]) 2 (.base 6 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113f24 loadLimbsBytes 7 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.left 16 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13f2f (by decide))
  advance_then (mov_r64_m64_effect_step 0x113f2f 0x48
    (by simp [RexWPrefix]) 1 (.base 6 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113f24 loadLimbsBytes 11 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.left 24 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13f33 (by decide))
  advance_then (mov_r64_m64_effect_step 0x113f33 0x4c
    (by simp [RexWPrefix]) 6 (.base 2 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113f24 loadLimbsBytes 15 3
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.right 0 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13f36 (by decide))
  advance_then (mov_r64_m64_effect_step 0x113f36 0x48
    (by simp [RexWPrefix]) 3 (.base 2 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113f24 loadLimbsBytes 18 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.right 8 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13f3a (by decide))
  advance_then (mov_r64_m64_effect_step 0x113f3a 0x4c
    (by simp [RexWPrefix]) 3 (.base 2 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113f24 loadLimbsBytes 22 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.right 16 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13f3e (by decide))
  advance_then (mov_r64_m64_effect_step 0x113f3e 0x48
    (by simp [RexWPrefix]) 6 (.base 2 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113f24 loadLimbsBytes 26 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.right 24 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13f42 (by decide))
  advance_finish [loadLimbsEffect]

theorem loadLimbsBytes_code :
    P256.Spec.Program.Extracted.textBytes.toListFrom 0x13f24 30 = loadLimbsBytes := by
  decide +kernel

end P256.Proofs.Field.Subtract
