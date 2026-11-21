import P256.Proofs.Verifying.Combination.Naf.Interface
import P256.Proofs.Verifying.Combination.Naf.Machine.Setup
import P256.Proofs.Common.Instructions.MovzxByte

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)

namespace P256.Proofs.Verifying.Combination.Naf.Machine

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Common.Instructions.CrossPageStore
open P256.Proofs.Common.Instructions.MovzxByte

structure ConstantsPre (s : RamState) : Prop where
  rip : s.RIP = 0x10f39b
  writable : Writable s (rspOf s) 48
  apart : RangeApart (rspOf s) 48 0x10f39b 39

def constantsBytes : List UInt8 :=
  [0x4c,0x89,0x3c,0x24,0x48,0x8d,0x43,0xff,0x48,0x89,0x44,0x24,0x28,
   0x48,0x89,0xd8,0x48,0xd1,0xe8,0x48,0x89,0x44,0x24,0x20,0x0f,0xb6,0xc3,
   0x89,0x44,0x24,0x0c,0x31,0xed,0x45,0x31,0xff,0x45,0x31,0xed]

def constantsEffect (s : RamState) : Effect :=
  { rip := 0x10f3c2
    writes := [⟨(Operand.mem (rspOf s) : Operand 64), (Operand.reg 15 : Operand 64).read s⟩,
      ⟨(Operand.mem (rspOf s+40) : Operand 64), (Operand.reg 3 : Operand 64).read s + (-1)⟩,
      ⟨(Operand.mem (rspOf s+32) : Operand 64), (Operand.reg 3 : Operand 64).read s >>> 1⟩,
      ⟨(Operand.reg 0 : Operand 64), (((Operand.reg 3 : Operand 64).read s).setWidth 8).setWidth 64⟩,
      ⟨(Operand.mem (rspOf s+12) : Operand 32), (((Operand.reg 3 : Operand 64).read s).setWidth 8).setWidth 32⟩,
      ⟨(Operand.reg 5 : Operand 64), 0⟩, ⟨(Operand.reg 15 : Operand 64), 0⟩,
      ⟨(Operand.reg 13 : Operand 64), 0⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

set_option maxHeartbeats 800000 in
theorem constants_block [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary ConstantsPre (codeRange 0x10f39b constantsBytes)
      (Effect.post constantsEffect) := by
  have next (offset : Nat) (bound : offset < 118431) :=
    boundary_ne_program hout (inProgram_of_textOffset offset bound)
  advance_begin (mov_m64_r64_effect_step_any 0x10f39b 0x4c (by simp [RexWPrefix]) 7 (.sib 4 none 0 .none) (by decide) rfl rfl)
  case pre =>
    intro s hp
    refine ⟨hp.rip, ?_, ?_⟩
    · change Writable s (rspOf s + 0#64) 8
      exact hp.writable.add 0 (by decide)
    · change RangeApart (rspOf s + 0#64) 8 0x10f39b 4
      intro i hi j hj eq
      exact hp.apart i (by omega) j (by omega) (by simpa only [BitVec.add_zero] using eq)
  case av =>
    intro s hp
    apply Effect.avoids_codeRange
    x86_norm
    exact P256.Proofs.Common.Instructions.RangeApart.add_left (h := hp.apart) 0 (by decide)
  case next => intro _ _; exact next 0xf39f (by decide)
  advance_then (lea_r64_effect_step 0x10f39f 0x48 (by simp [RexWPrefix]) 0 (.base 3 (.d8 255)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f39b constantsBytes 4 4
  case mid =>
    intro s t hp he ho
    exact ⟨he.rip_of (by x86_norm), Effect.Avoids.of_noMem
      (by simp [Component.Covers]) _, next 0xf3a3 (by decide)⟩
  advance_then (mov_m64_r64_effect_step_any 0x10f3a3 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 40)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f39b constantsBytes 8 5
  case mid =>
    intro s t hp he ho
    refine ⟨Pre.of_holds he (ho true) (by x86_norm) ?_ ?_,
      Effect.Local.avoids (by x86_local) (ho true) ?_, next 0xf3a8 (by decide)⟩
    · x86_norm
      exact hp.writable.add 40 (by decide)
    · x86_norm
      intro i hi j hj eq
      apply hp.apart (40+i) (by omega) (8+j) (by omega)
      simpa only [rspOf, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using eq
    · apply Effect.avoids_codeRange
      x86_norm
      exact P256.Proofs.Common.Instructions.RangeApart.add_left (h := hp.apart) 40 (by decide)
  advance_then (mov_r64_r64_effect_step 0x10f3a8 0x48 0xd8 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10f39b constantsBytes 13 3
  case mid =>
    intro s t hp he ho
    exact ⟨he.rip_of (by x86_norm), Effect.Avoids.of_noMem
      (by simp [Component.Covers]) _, next 0xf3ab (by decide)⟩
  advance_then (shr_r64_one_effect_step 0x10f3ab 0x48 0xe8 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f39b constantsBytes 16 3
  case mid =>
    intro s t hp he ho
    exact ⟨he.rip_of (by x86_norm), Effect.Avoids.of_noMem
      (by simp [Component.Covers]) _, next 0xf3ae (by decide)⟩
  advance_then (mov_m64_r64_effect_step_any 0x10f3ae 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 32)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f39b constantsBytes 19 5
  case mid =>
    intro s t hp he ho
    refine ⟨Pre.of_holds he (ho true) (by x86_norm) ?_ ?_,
      Effect.Local.avoids (by x86_local) (ho true) ?_, next 0xf3b3 (by decide)⟩
    · x86_norm
      exact hp.writable.add 32 (by decide)
    · x86_norm
      intro i hi j hj eq
      apply hp.apart (32+i) (by omega) (19+j) (by omega)
      simpa only [rspOf, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using eq
    · apply Effect.avoids_codeRange
      x86_norm
      exact P256.Proofs.Common.Instructions.RangeApart.add_left (h := hp.apart) 32 (by decide)
  advance_then (movzx_r32_r8_effect_step 0x10f3b3 0xc3 rfl (by decide))
  case sub => exact codeRange_slice_subset 0x10f39b constantsBytes 24 3
  case mid =>
    intro s t hp he ho
    exact ⟨he.rip_of (by x86_norm), Effect.Avoids.of_noMem
      (by simp [movzxR32R8Effect, Effect.components, Component.Covers]) _, next 0xf3b6 (by decide)⟩
  advance_then (mov_m32_r32_legacy_effect_step_any 0x10f3b6 0 (.sib 4 none 0 (.d8 12)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f39b constantsBytes 27 4
  case mid =>
    intro s t hp he ho
    refine ⟨Pre.of_holds he (ho true) (by x86_norm) ?_ ?_,
      Effect.Local.avoids (by x86_local) (ho true) ?_, next 0xf3ba (by decide)⟩
    · x86_norm
      exact hp.writable.add 12 (by decide)
    · x86_norm
      intro i hi j hj eq
      apply hp.apart (12+i) (by omega) (27+j) (by omega)
      simpa only [rspOf, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using eq
    · apply Effect.avoids_codeRange
      x86_norm
      exact P256.Proofs.Common.Instructions.RangeApart.add_left (h := hp.apart) 12 (by decide)
  advance_then (show StepEffect _ _ (xorR32R32Effect 0x10f3ba 2 5 5) from xor_r32_r32_effect_step 0x10f3ba 0xed rfl)
  case sub => exact codeRange_slice_subset 0x10f39b constantsBytes 31 2
  case mid =>
    intro s t hp he ho
    exact ⟨he.rip_of (by x86_norm), Effect.Avoids.of_noMem
      (by simp [Component.Covers]) _, next 0xf3bc (by decide)⟩
  advance_then (show StepEffect _ _ (xorR32R32Effect 0x10f3bc 3 15 15) from xor_r32_r32_rex_effect_step 0x10f3bc 0x45 0xff (by simp [RexNoWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10f39b constantsBytes 33 3
  case mid =>
    intro s t hp he ho
    exact ⟨he.rip_of (by x86_norm), Effect.Avoids.of_noMem
      (by simp [Component.Covers]) _, next 0xf3bf (by decide)⟩
  advance_then (show StepEffect _ _ (xorR32R32Effect 0x10f3bf 3 13 13) from xor_r32_r32_rex_effect_step 0x10f3bf 0x45 0xed (by simp [RexNoWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10f39b constantsBytes 36 3
  case mid =>
    intro s t hp he ho
    exact ⟨he.rip_of (by x86_norm), Effect.Avoids.of_noMem
      (by simp [Component.Covers]) _, next 0xf3c2 (by decide)⟩
  have narrow (x : BitVec 8) : (x.setWidth 64).setWidth 32 = x.setWidth 32 :=
    BitVec.setWidth_setWidth_of_le x (by decide)
  apply AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · x86_norm [constantsEffect, BitVec.add_zero, narrow]
  · x86_norm [constantsEffect, BitVec.xor_self, BitVec.add_zero, narrow]
    repeat first
      | apply And.intro
      | rfl
      | exact Or.inl rfl
      | exact Or.inr (Or.inl rfl)
      | exact Or.inr (Or.inr (Or.inl rfl))
      | exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · intro i
    cases i <;> x86_norm [constantsEffect, BitVec.add_zero, narrow]
  · x86_norm [constantsEffect, BitVec.add_zero, narrow]

end P256.Proofs.Verifying.Combination.Naf.Machine
