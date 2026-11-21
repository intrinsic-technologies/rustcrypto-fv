import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Instructions.CrossPageStore
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.Common.Field

structure ConstantsPre (s : RamState) : Prop where
  rip : s.RIP = 0x10d599
  writable : ∀ offset len : Nat, offset + len ≤ 576 → 0 < len →
    P256.Proofs.Common.Instructions.CrossPageStore.Writable s
      (stackPtr s + BitVec.ofNat 64 offset) len
  codeApart : ∀ offset len : Nat, offset + len ≤ 576 →
    ∀ codeOffset codeLen : Nat, codeOffset + codeLen ≤ 118431 →
    RangeApart (stackPtr s + BitVec.ofNat 64 offset) len
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) codeLen

def constantsBytes : List UInt8 :=
  [0x48, 0xb8, 0xab, 0xd9, 0x83, 0x1f, 0x19, 0xcd, 0xe0, 0x5b, 0x48, 0x89, 0x84, 0x24, 0x30, 0x2, 0x0, 0x0, 0x48, 0xb8, 0x7f, 0x52, 0xe, 0x51, 0x8c, 0x68, 0x5, 0x9b, 0x48, 0x89, 0x84, 0x24, 0x28, 0x2, 0x0, 0x0, 0x48, 0xb8, 0x72, 0xf3, 0x6e, 0x3c, 0x3a, 0xf5, 0x4f, 0xa5, 0x48, 0x89, 0x84, 0x24, 0x20, 0x2, 0x0, 0x0, 0x48, 0xb8, 0x67, 0xe6, 0x9, 0x6a, 0x85, 0xae, 0x67, 0xbb, 0x48, 0x89, 0x84, 0x24, 0x18, 0x2, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0x38, 0x2, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0xc6, 0x84, 0x24, 0x17, 0x2, 0x0, 0x0, 0x0]

def constantsEffect (s : RamState) : Effect :=
  { rip := 0x10d5f5
    writes := [
      ⟨(.reg 0 : Operand 64), 0xbb67ae856a09e667⟩,
      ⟨(.mem (stackPtr s + 560) : Operand 64), 0x5be0cd191f83d9ab⟩,
      ⟨(.mem (stackPtr s + 552) : Operand 64), 0x9b05688c510e527f⟩,
      ⟨(.mem (stackPtr s + 544) : Operand 64), 0xa54ff53a3c6ef372⟩,
      ⟨(.mem (stackPtr s + 536) : Operand 64), 0xbb67ae856a09e667⟩,
      ⟨(.mem (stackPtr s + 568) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 535) : Operand 8), 0⟩] }

set_option maxHeartbeats 800000 in
theorem constants_run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary ConstantsPre (codeRange 0x10d599 constantsBytes)
      (Effect.post constantsEffect) := by
  advance_begin (mov_r64_imm64_effect_step 0x10d599 0x48 0xb8 (by simp [RexWPrefix]) (by decide) 0x5be0cd191f83d9ab)
  case next => intro s hP; exact boundary_ne_program outside (inProgram_of_textOffset 0xd5a3 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10d5a3 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 560)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d599 constantsBytes 10 8
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 560 8 (by decide) (by decide)
    · x86_norm
      exact hP.codeApart 560 8 (by decide) 0xd5a3 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 560 8 (by decide) 0xd599 92 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd5ab (by decide))
  advance_then (mov_r64_imm64_effect_step 0x10d5ab 0x48 0xb8 (by simp [RexWPrefix]) (by decide) 0x9b05688c510e527f)
  case sub => exact codeRange_slice_subset 0x10d599 constantsBytes 18 10
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd5b5 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10d5b5 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 552)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d599 constantsBytes 28 8
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 552 8 (by decide) (by decide)
    · x86_norm
      exact hP.codeApart 552 8 (by decide) 0xd5b5 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 552 8 (by decide) 0xd599 92 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd5bd (by decide))
  advance_then (mov_r64_imm64_effect_step 0x10d5bd 0x48 0xb8 (by simp [RexWPrefix]) (by decide) 0xa54ff53a3c6ef372)
  case sub => exact codeRange_slice_subset 0x10d599 constantsBytes 36 10
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd5c7 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10d5c7 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 544)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d599 constantsBytes 46 8
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 544 8 (by decide) (by decide)
    · x86_norm
      exact hP.codeApart 544 8 (by decide) 0xd5c7 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 544 8 (by decide) 0xd599 92 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd5cf (by decide))
  advance_then (mov_r64_imm64_effect_step 0x10d5cf 0x48 0xb8 (by simp [RexWPrefix]) (by decide) 0xbb67ae856a09e667)
  case sub => exact codeRange_slice_subset 0x10d599 constantsBytes 54 10
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd5d9 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10d5d9 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 536)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d599 constantsBytes 64 8
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 536 8 (by decide) (by decide)
    · x86_norm
      exact hP.codeApart 536 8 (by decide) 0xd5d9 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 536 8 (by decide) 0xd599 92 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd5e1 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x10d5e1 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d32 568)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10d599 constantsBytes 72 12
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 568 8 (by decide) (by decide)
    · x86_norm
      exact hP.codeApart 568 8 (by decide) 0xd5e1 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 568 8 (by decide) 0xd599 92 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd5ed (by decide))
  advance_then (mov_m8_imm8_effect_step 0x10d5ed (.sib 4 none 0 (.d32 535))
    (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10d599 constantsBytes 84 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      have hw := hP.writable 535 1 (by decide) (by decide)
      exact ⟨hw.low, hw.mem, hw.tables⟩
    · x86_norm
      exact hP.codeApart 535 1 (by decide) 0xd5ed 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 535 1 (by decide) 0xd599 92 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd5f5 (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  have rsp : (Operand.reg 4 : Operand 64).read s = stackPtr s := rfl
  apply hH.weaken
  · x86_norm [constantsEffect, rsp]
  · x86_norm [constantsEffect, rsp]
    all_goals (repeat constructor <;> rfl)
  · intro i; cases i <;> x86_norm [constantsEffect, rsp]
  · x86_norm [constantsEffect, rsp]

end P256.Proofs.Verifying.Message
