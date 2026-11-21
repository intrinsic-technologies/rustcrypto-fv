import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Instructions.CrossPageStore
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.Common.Field

structure ConstantsPre (s : RamState) : Prop where
  rip : s.RIP = 0x102720
  writable : ∀ offset len : Nat, offset + len ≤ 280 → 0 < len →
    P256.Proofs.Common.Instructions.CrossPageStore.Writable s
      (stackPtr s + BitVec.ofNat 64 offset) len
  codeApart : ∀ offset len : Nat, offset + len ≤ 280 →
    ∀ codeOffset codeLen : Nat, codeOffset + codeLen ≤ 118431 →
    RangeApart (stackPtr s + BitVec.ofNat 64 offset) len
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) codeLen

def constantsBytes : List UInt8 :=
  [0x48,0xb8,0xab,0xd9,0x83,0x1f,0x19,0xcd,0xe0,0x5b,0x48,0x89,0x84,0x24,0x8,0x1,0x0,0x0,0x48,0xb8,0x7f,0x52,0xe,0x51,0x8c,0x68,0x5,0x9b,0x48,0x89,0x84,0x24,0x0,0x1,0x0,0x0,0x48,0xb8,0x72,0xf3,0x6e,0x3c,0x3a,0xf5,0x4f,0xa5,0x48,0x89,0x84,0x24,0xf8,0x0,0x0,0x0,0x48,0xb8,0x67,0xe6,0x9,0x6a,0x85,0xae,0x67,0xbb,0x48,0x89,0x84,0x24,0xf0,0x0,0x0,0x0,0x48,0xc7,0x84,0x24,0x10,0x1,0x0,0x0,0x0,0x0,0x0,0x0,0xc6,0x84,0x24,0xef,0x0,0x0,0x0,0x0]

def constantsEffect (s : RamState) : Effect :=
  { rip := 0x10277c
    writes := [
      ⟨(.reg 0 : Operand 64), 0xbb67ae856a09e667⟩,
      ⟨(.mem (stackPtr s + 264) : Operand 64), 0x5be0cd191f83d9ab⟩,
      ⟨(.mem (stackPtr s + 256) : Operand 64), 0x9b05688c510e527f⟩,
      ⟨(.mem (stackPtr s + 248) : Operand 64), 0xa54ff53a3c6ef372⟩,
      ⟨(.mem (stackPtr s + 240) : Operand 64), 0xbb67ae856a09e667⟩,
      ⟨(.mem (stackPtr s + 272) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 239) : Operand 8), 0⟩] }

set_option maxHeartbeats 800000 in
theorem constants_run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary ConstantsPre (codeRange 0x102720 constantsBytes)
      (Effect.post constantsEffect) := by
  advance_begin (mov_r64_imm64_effect_step 0x102720 0x48 0xb8 (by simp [RexWPrefix]) (by decide) 0x5be0cd191f83d9ab)
  case next => intro s hP; exact boundary_ne_program outside (inProgram_of_textOffset 0x272a (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10272a 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 264)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x102720 constantsBytes 10 8
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 264 8 (by decide) (by decide)
    · x86_norm
      exact hP.codeApart 264 8 (by decide) 0x272a 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 264 8 (by decide) 0x2720 92 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2732 (by decide))
  advance_then (mov_r64_imm64_effect_step 0x102732 0x48 0xb8 (by simp [RexWPrefix]) (by decide) 0x9b05688c510e527f)
  case sub => exact codeRange_slice_subset 0x102720 constantsBytes 18 10
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x273c (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10273c 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 256)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x102720 constantsBytes 28 8
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 256 8 (by decide) (by decide)
    · x86_norm
      exact hP.codeApart 256 8 (by decide) 0x273c 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 256 8 (by decide) 0x2720 92 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2744 (by decide))
  advance_then (mov_r64_imm64_effect_step 0x102744 0x48 0xb8 (by simp [RexWPrefix]) (by decide) 0xa54ff53a3c6ef372)
  case sub => exact codeRange_slice_subset 0x102720 constantsBytes 36 10
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x274e (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10274e 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 248)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x102720 constantsBytes 46 8
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 248 8 (by decide) (by decide)
    · x86_norm
      exact hP.codeApart 248 8 (by decide) 0x274e 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 248 8 (by decide) 0x2720 92 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2756 (by decide))
  advance_then (mov_r64_imm64_effect_step 0x102756 0x48 0xb8 (by simp [RexWPrefix]) (by decide) 0xbb67ae856a09e667)
  case sub => exact codeRange_slice_subset 0x102720 constantsBytes 54 10
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2760 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x102760 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 240)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x102720 constantsBytes 64 8
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 240 8 (by decide) (by decide)
    · x86_norm
      exact hP.codeApart 240 8 (by decide) 0x2760 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 240 8 (by decide) 0x2720 92 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2768 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x102768 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d32 272)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x102720 constantsBytes 72 12
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 272 8 (by decide) (by decide)
    · x86_norm
      exact hP.codeApart 272 8 (by decide) 0x2768 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 272 8 (by decide) 0x2720 92 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2774 (by decide))
  advance_then (mov_m8_imm8_effect_step 0x102774 (.sib 4 none 0 (.d32 239))
    (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x102720 constantsBytes 84 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      have hw := hP.writable 239 1 (by decide) (by decide)
      exact ⟨hw.low, hw.mem, hw.tables⟩
    · x86_norm
      exact hP.codeApart 239 1 (by decide) 0x2774 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 239 1 (by decide) 0x2720 92 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x277c (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  have rsp : (Operand.reg 4 : Operand 64).read s = stackPtr s := rfl
  apply hH.weaken
  · x86_norm [constantsEffect, rsp]
  · x86_norm [constantsEffect, rsp]
    all_goals (repeat constructor <;> rfl)
  · intro i; cases i <;> x86_norm [constantsEffect, rsp]
  · x86_norm [constantsEffect, rsp]

end P256.Proofs.Signing.Wrapper.Hash
