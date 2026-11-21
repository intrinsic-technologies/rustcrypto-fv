import P256.Proofs.Verifying.Core.Memory
import P256.Proofs.Verifying.Core.Prepare.Pointers
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Instructions.CrossPageStore
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Digest.Setup

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field

structure InitializePre (s : RamState) : Prop where
  rip : s.RIP = 0x10dbda
  bitsWritable : P256.Proofs.Common.Instructions.CrossPageStore.Writable s (rspOf s+576) 4
  writable : ∀ i ∈ [0,8,16,24], MemWritable s (rspOf s+i) 8
  bitsApart : ∀ off len : Nat, off+len ≤ 118431 →
    RangeApart (rspOf s+576) 4 (Extracted.textAddress + BitVec.ofNat 64 off) len
  wordsApart : ∀ i ∈ [0,8,16,24], ∀ off len : Nat, off+len ≤ 118431 →
    RangeApart (rspOf s+i) 8 (Extracted.textAddress + BitVec.ofNat 64 off) len

def initializeBytes : List UInt8 :=
  [0xc7, 0x84, 0x24, 0x40, 0x2, 0x0, 0x0, 0x0, 0x1, 0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x18, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x10, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x8, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x4, 0x24, 0x0, 0x0, 0x0, 0x0, 0x48, 0x8d, 0xbc, 0x24, 0xa8, 0x1, 0x0, 0x0, 0x48, 0x89, 0xe2, 0xbe, 0x20, 0x0, 0x0, 0x0, 0xb9, 0x4, 0x0, 0x0, 0x0, 0x41, 0xb8, 0x0, 0x1, 0x0, 0x0]

def initializeEffect (s : RamState) : Effect :=
  { rip := 0x10dc23
    writes := [⟨(.mem (rspOf s+576) : Operand 32), 256⟩,
      ⟨(.mem (rspOf s+24) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s+16) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s+8) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s+0) : Operand 64), 0⟩,
      ⟨(.reg 7 : Operand 64), rspOf s+424⟩,
      ⟨(.reg 2 : Operand 64), rspOf s+0⟩,
      ⟨(.reg 6 : Operand 64), 32⟩,
      ⟨(.reg 1 : Operand 64), 4⟩,
      ⟨(.reg 8 : Operand 64), 256⟩] }

set_option maxHeartbeats 800000 in
theorem initialize_block [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary InitializePre (codeRange 0x10dbda initializeBytes) (Effect.post initializeEffect) := by
  advance_begin (P256.Proofs.Common.Instructions.CrossPageStore.mov_m32_imm32_legacy_effect_step_any
    0x10dbda (.sib 4 none 0 (.d32 576)) (by decide) rfl rfl 256)
  case pre =>
    intro s hp
    exact ⟨hp.rip, hp.bitsWritable, hp.bitsApart 0xdbda 11 (by decide)⟩
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0xdbe5 (by decide))
  case av =>
    intro s hp
    apply Effect.avoids_codeRange
    x86_norm
    exact hp.bitsApart 0xdbda 73 (by decide)
  advance_then (mov_m64_imm32_effect_step 0x10dbe5 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d8 24)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10dbda initializeBytes 11 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 24 (by simp)
    · x86_norm
      exact hP.wordsApart 24 (by simp) 0xdbe5 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.wordsApart 24 (by simp) 0xdbda 73 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xdbee (by decide))
  advance_then (mov_m64_imm32_effect_step 0x10dbee 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d8 16)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10dbda initializeBytes 20 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 16 (by simp)
    · x86_norm
      exact hP.wordsApart 16 (by simp) 0xdbee 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.wordsApart 16 (by simp) 0xdbda 73 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xdbf7 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x10dbf7 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10dbda initializeBytes 29 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 8 (by simp)
    · x86_norm
      exact hP.wordsApart 8 (by simp) 0xdbf7 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.wordsApart 8 (by simp) 0xdbda 73 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xdc00 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x10dc00 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 .none) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10dbda initializeBytes 38 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 0 (by simp)
    · x86_norm
      exact hP.wordsApart 0 (by simp) 0xdc00 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.wordsApart 0 (by simp) 0xdbda 73 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xdc08 (by decide))
  advance_then (lea_r64_effect_step 0x10dc08 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 424)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dbda initializeBytes 46 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xdc10 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10dc10 0x48 0xe2 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10dbda initializeBytes 54 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xdc13 (by decide))⟩
  advance_then (mov_r32_imm32_effect_step 0x10dc13 0xbe (by decide) 32)
  case sub => exact codeRange_slice_subset 0x10dbda initializeBytes 57 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xdc18 (by decide))⟩
  advance_then (mov_r32_imm32_effect_step 0x10dc18 0xb9 (by decide) 4)
  case sub => exact codeRange_slice_subset 0x10dbda initializeBytes 62 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xdc1d (by decide))⟩
  advance_then (mov_r32_imm32_rex_effect_step 0x10dc1d 0x41 0xb8 (by simp [RexNoWPrefix]) (by decide) 256)
  case sub => exact codeRange_slice_subset 0x10dbda initializeBytes 67 6
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xdc23 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hp hh
  apply hh.weaken
  · x86_norm [initializeEffect]
  · x86_norm [initializeEffect]
    exact Or.inr (by rw [BitVec.add_zero]; rfl)
  · intro i
    cases i <;> x86_norm [initializeEffect]
  · x86_norm [initializeEffect]

end P256.Proofs.Verifying.Core.Digest.Setup
