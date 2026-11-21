import P256.Proofs.Verifying.Combination.Naf.Interface
import P256.Proofs.Verifying.Combination.Naf.Machine.Setup
import X86Proofs.Instructions.Test.Generated.RR.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)

namespace P256.Proofs.Verifying.Combination.Naf.Machine

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar

structure LoopPrefixPre (s : RamState) : Prop where
  rip : s.RIP = 0x10f38a
  writable : MemWritable s (rspOf s + 24) 8
  apart : RangeApart (rspOf s + 24) 8 0x10f38a 11

def loopPrefixBytes : List UInt8 :=
  [0x45,0x31,0xf6,0x4c,0x89,0x6c,0x24,0x18,0x4d,0x85,0xed]

def loopPrefixEffect (s : RamState) : Effect :=
  { rip := 0x10f395
    writes := [⟨(Operand.reg 14 : Operand 64), 0⟩,
      ⟨(Operand.mem (rspOf s+24) : Operand 64), (Operand.reg 13 : Operand 64).read s⟩]
    flags := some ⟨none,none,none,some ((Operand.reg 13 : Operand 64).read s == 0),none,none⟩ }

theorem loop_prefix_block [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary LoopPrefixPre (codeRange 0x10f38a loopPrefixBytes)
      (Effect.post loopPrefixEffect) := by
  have next (offset : Nat) (bound : offset < 118431) :=
    boundary_ne_program hout (inProgram_of_textOffset offset bound)
  advance_begin (show StepEffect _ _ (xorR32R32Effect 0x10f38a 3 14 14) from
    xor_r32_r32_rex_effect_step 0x10f38a 0x45 0xf6 (by simp [RexNoWPrefix]) rfl)
  case next => intro _ _; exact next 0xf38d (by decide)
  advance_then (mov_m64_r64_effect_step 0x10f38d 0x4c (by simp [RexWPrefix]) 5
    (.sib 4 none 0 (.d8 24)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f38a loopPrefixBytes 3 5
  case mid =>
    intro s t hp he ho
    refine ⟨StorePre.of_holds he (ho true) (by x86_norm) (by x86_addr_obs) ?_ ?_,
      Effect.Local.avoids (by x86_local) (ho true) ?_, next 0xf392 (by decide)⟩
    · x86_norm
      exact hp.writable
    · x86_norm
      intro i hi j hj eq
      apply hp.apart i hi (3+j) (by omega)
      simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, rspOf] using eq
    · apply Effect.avoids_codeRange
      x86_norm
      exact hp.apart
  advance_then (show StepEffect _ _ (testR64R64Effect 0x10f392 13 13) from
    test_r64_r64_effect_step 0x10f392 0x4d 0xed (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10f38a loopPrefixBytes 8 3
  case mid =>
    intro s t hp he ho
    exact ⟨he.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, next 0xf395 (by decide)⟩
  apply AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · x86_norm [loopPrefixEffect, BitVec.xor_self, BitVec.and_self]
  · x86_norm [loopPrefixEffect, BitVec.xor_self, BitVec.and_self]
    repeat constructor
  · intro i
    cases i <;> x86_norm [loopPrefixEffect, testFlags, BitVec.and_self]
  · x86_norm [loopPrefixEffect, BitVec.xor_self, BitVec.and_self]

end P256.Proofs.Verifying.Combination.Naf.Machine
