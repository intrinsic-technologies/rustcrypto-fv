import P256.Proofs.Verifying.Combination.Naf.Interface
import P256.Proofs.Verifying.Combination.Naf.Machine.Setup
import P256.Proofs.Common.Field.Operations.Neg.Borrow.Or
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)

namespace P256.Proofs.Verifying.Combination.Naf.Machine.WindowMachine

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Verifying.Combination.Naf.Machine.Instructions.ShiftCount
open P256.Proofs.Common.Field.FieldNeg.Instructions

attribute [local x86_compose] jmpEffect branchEffect

def crossBytes : List UInt8 :=
  [0x89,0xd9,0x48,0xd3,0xe8,0x89,0xe9,0x48,0xd3,0xe2,0x48,0x9,0xc2]

def crossEffect (s : RamState) : Effect :=
  { rip := 0x10f42d
    writes := [⟨(Operand.reg 0 : Operand 64),
      (Operand.reg 0 : Operand 64).read s >>> shiftCount 64 ((Operand.reg 3 : Operand 8).read s)⟩,
      ⟨(Operand.reg 1 : Operand 64), ((Operand.reg 5 : Operand 32).read s).setWidth 64⟩,
      ⟨(Operand.reg 2 : Operand 64), ((Operand.reg 2 : Operand 64).read s <<< shiftCount 64 ((Operand.reg 5 : Operand 8).read s)) ||| ((Operand.reg 0 : Operand 64).read s >>> shiftCount 64 ((Operand.reg 3 : Operand 8).read s))⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

theorem cross_block [Bindings] (boundary : ReturnBoundary) (outer : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP=0x10f420) (codeRange 0x10f420 crossBytes)
      (Effect.post crossEffect) := by
  have next (offset : Nat) (bound : offset<118431) :=
    boundary_ne_program outer (inProgram_of_textOffset offset bound)
  have narrow (s : RamState) (r : BitVec 5) :
      (((Operand.reg r : Operand 32).read s).setWidth 64).setWidth 8=(Operand.reg r : Operand 8).read s := by
    change (((Operand.reg r : Operand 64).read s).setWidth 32 |>.setWidth 64 |>.setWidth 8)=_
    rw [BitVec.setWidth_setWidth_of_le _ (by decide),BitVec.setWidth_setWidth_of_le _ (by decide)]
    rfl
  advance_begin (show StepEffect _ _ (movR32R32Effect 0x10f420 2 1 3) from mov_r32_r32_effect_step 0x10f420 0xd9 rfl)
  case next => intro _ _; exact next 0xf422 (by decide)
  advance_then (show StepEffect _ _ (shrR64CLEffect 0x10f422 0) from shr_r64_cl_effect_step 0x10f422 0x48 0xe8 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f420 crossBytes 2 3
  case mid =>
    intro s t hp he ho
    exact ⟨he.rip_of (by x86_norm), Effect.Avoids.of_noMem
      (by simp [shrR64CLEffect, Component.Covers]) _, next 0xf425 (by decide)⟩
  advance_then (show StepEffect _ _ (movR32R32Effect 0x10f425 2 1 5) from mov_r32_r32_effect_step 0x10f425 0xe9 rfl)
  case sub => exact codeRange_slice_subset 0x10f420 crossBytes 5 2
  case mid =>
    intro s t hp he ho
    exact ⟨he.rip_of (by x86_norm), Effect.Avoids.of_noMem
      (by simp [Component.Covers]) _, next 0xf427 (by decide)⟩
  advance_then (show StepEffect _ _ (shlR64CLEffect 0x10f427 2) from shl_r64_cl_effect_step 0x10f427 0x48 0xe2 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f420 crossBytes 7 3
  case mid =>
    intro s t hp he ho
    exact ⟨he.rip_of (by x86_norm), Effect.Avoids.of_noMem
      (by simp [shlR64CLEffect, P256.Proofs.Common.Instructions.ShiftLeft.shlR64Effect, Effect.components, Component.Covers]) _, next 0xf42a (by decide)⟩
  advance_then (show StepEffect _ _ (orR64R64Effect 0x10f42a 2 0) from or_r64_r64_effect_step 0x10f42a 0x48 0xc2 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10f420 crossBytes 10 3
  case mid =>
    intro s t hp he ho
    exact ⟨he.rip_of (by x86_norm), Effect.Avoids.of_noMem
      (by simp [orR64R64Effect, Effect.components, Component.Covers]) _, next 0xf42d (by decide)⟩
  apply AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · x86_norm [crossEffect,narrow]
  · x86_norm [crossEffect,narrow]
    repeat constructor
  · intro i
    cases i <;> x86_norm [crossEffect]
  · x86_norm [crossEffect]

end P256.Proofs.Verifying.Combination.Naf.Machine.WindowMachine
