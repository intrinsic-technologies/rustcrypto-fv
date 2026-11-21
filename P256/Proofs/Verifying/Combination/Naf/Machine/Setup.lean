import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Verifying.Combination.Naf.Machine.Instructions.ShiftCount.Triple
import P256.Proofs.Program.Code
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

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)

namespace P256.Proofs.Verifying.Combination.Naf.Machine

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Common.Instructions.CrossPageStore
open P256.Proofs.Verifying.Combination.Naf.Machine.Instructions.ShiftCount

structure SetupPre (s : RamState) : Prop where
  rip : s.RIP = 0x10f35e
  writable : Writable s ((Operand.reg 4 : Operand 64).read s + 16) 8
  apart : RangeApart ((Operand.reg 4 : Operand 64).read s + 16) 8 0x10f35e 39

def setupBytes : List UInt8 :=
  [0x4d,0x89,0xcc,0x4d,0x89,0xc5,0x48,0x89,0xc8,0x49,0x89,0xf7,
   0x48,0x89,0x7c,0x24,0x10,0xbb,1,0,0,0,0x44,0x89,0xe1,
   0x48,0xd3,0xe3,0x48,0x8d,0x7c,0x24,0x30,0x48,0x89,0xd6,0x48,0x89,0xc2]

def setupEffect (s : RamState) : Effect :=
  { rip := 0x10f385
    writes := [⟨(Operand.reg 12 : Operand 64), (Operand.reg 9 : Operand 64).read s⟩,
      ⟨(Operand.reg 13 : Operand 64), (Operand.reg 8 : Operand 64).read s⟩,
      ⟨(Operand.reg 0 : Operand 64), (Operand.reg 1 : Operand 64).read s⟩,
      ⟨(Operand.reg 15 : Operand 64), (Operand.reg 6 : Operand 64).read s⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 16) : Operand 64), (Operand.reg 7 : Operand 64).read s⟩,
      ⟨(Operand.reg 3 : Operand 64), (1#64) <<< shiftCount 64 (((Operand.reg 9 : Operand 64).read s).setWidth 8)⟩,
      ⟨(Operand.reg 1 : Operand 64), (((Operand.reg 9 : Operand 64).read s).setWidth 32).setWidth 64⟩,
      ⟨(Operand.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s + 48⟩,
      ⟨(Operand.reg 6 : Operand 64), (Operand.reg 2 : Operand 64).read s⟩,
      ⟨(Operand.reg 2 : Operand 64), (Operand.reg 1 : Operand 64).read s⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

set_option maxHeartbeats 800000 in
theorem setup_block [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary SetupPre (codeRange 0x10f35e setupBytes) (Effect.post setupEffect) := by
  have next (offset : Nat) (bound : offset < 118431) :=
    boundary_ne_program hout (inProgram_of_textOffset offset bound)
  have narrow (t : RamState) (r : BitVec 5) :
      (((Operand.reg r : Operand 32).read t).setWidth 64).setWidth 8 = (Operand.reg r : Operand 8).read t := by
    simp only [Operand.read]
    rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_setWidth_of_le _ (by decide)]
  advance_begin (mov_r64_r64_effect_step 0x10f35e 0x4d 0xcc (by simp [RexWPrefix]) rfl)
  case next => intro _ _; exact next 0xf361 (by decide)
  advance_then (mov_r64_r64_effect_step 0x10f361 0x4d 0xc5 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10f35e setupBytes 3 3
  case mid =>
    intro s t hp he ho
    exact ⟨he.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, next 0xf364 (by decide)⟩
  advance_then (mov_r64_r64_effect_step 0x10f364 0x48 0xc8 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10f35e setupBytes 6 3
  case mid =>
    intro s t hp he ho
    exact ⟨he.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, next 0xf367 (by decide)⟩
  advance_then (mov_r64_r64_effect_step 0x10f367 0x49 0xf7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10f35e setupBytes 9 3
  case mid =>
    intro s t hp he ho
    exact ⟨he.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, next 0xf36a (by decide)⟩
  advance_then (mov_m64_r64_effect_step_any 0x10f36a 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d8 16)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f35e setupBytes 12 5
  case mid =>
    intro s t hp he ho
    refine ⟨Pre.of_holds he (ho true) (by x86_norm) ?_ ?_, ?_, next 0xf36f (by decide)⟩
    · x86_norm
      exact hp.writable
    · x86_norm
      intro i hi j hj eq
      apply hp.apart i hi (12+j) (by omega)
      simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using eq
    · apply Effect.avoids_codeRange
      intro c hc a len eq
      x86_norm at hc
      rcases hc with rfl | rfl
      · cases eq
        have sp : t.regValue .rsp = (Operand.reg 4 : Operand 64).read s := he.agrees.read (n := 64) (r := 4) (by simp only [Effect.components, List.map_cons, List.map_nil, Write.component, Operand.component, List.append_nil, List.cons_append, List.mem_cons]; decide)
        change RangeApart (t.regValue .rsp + 16) 8 0x10f35e 39
        rw [sp]
        exact hp.apart
      · cases eq
  advance_then (mov_r32_imm32_effect_step 0x10f36f 0xbb (by decide) 1)
  case sub => exact codeRange_slice_subset 0x10f35e setupBytes 17 5
  case mid =>
    intro s t hp he ho
    exact ⟨he.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, next 0xf374 (by decide)⟩
  advance_then (mov_r32_r32_rex_effect_step 0x10f374 0x44 0xe1 (by simp [RexNoWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10f35e setupBytes 22 3
  case mid =>
    intro s t hp he ho
    exact ⟨he.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, next 0xf377 (by decide)⟩
  advance_then (shl_r64_cl_effect_step 0x10f377 0x48 0xe3 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f35e setupBytes 25 3
  case mid =>
    intro s t hp he ho
    exact ⟨he.rip_of (by x86_norm), Effect.Avoids.of_noMem
      (by simp [shlR64CLEffect, P256.Proofs.Common.Instructions.ShiftLeft.shlR64Effect,
        Effect.components, Component.Covers]) _, next 0xf37a (by decide)⟩
  advance_then (lea_r64_effect_step 0x10f37a 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d8 48)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f35e setupBytes 28 5
  case mid =>
    intro s t hp he ho
    exact ⟨he.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, next 0xf37f (by decide)⟩
  advance_then (mov_r64_r64_effect_step 0x10f37f 0x48 0xd6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10f35e setupBytes 33 3
  case mid =>
    intro s t hp he ho
    exact ⟨he.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, next 0xf382 (by decide)⟩
  advance_then (mov_r64_r64_effect_step 0x10f382 0x48 0xc2 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10f35e setupBytes 36 3
  case mid =>
    intro s t hp he ho
    exact ⟨he.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, next 0xf385 (by decide)⟩
  apply AdvanceTriple.block_end
  intro s t hp he
  apply he.weaken
  · x86_norm [setupEffect, narrow]
  · x86_norm [setupEffect, narrow]
    clear he hp
    repeat constructor
  · intro i
    cases i <;> x86_norm [setupEffect, narrow]
  · x86_norm [setupEffect, narrow]

end P256.Proofs.Verifying.Combination.Naf.Machine
