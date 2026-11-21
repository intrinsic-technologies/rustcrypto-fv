import P256.Proofs.Program.Code
import P256.Proofs.Common.Instructions.CrossPageStore.Immediate
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Sec1.Affine.Uncompressed.Curve

open P256.Spec.Program.Routines
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure BPre (s : RamState) : Prop where
  rip : s.RIP = 0x110b06
  writable : ∀ off ∈ ([16,24,32,40] : List (BitVec 64)),
    P256.Proofs.Common.Instructions.CrossPageStore.Writable s (stackPtr s + off) 8
  codeApart : ∀ off ∈ ([16,24,32,40] : List (BitVec 64)), ∀ offset len : Nat,
    offset + len ≤ 118431 → RangeApart (stackPtr s + off) 8
      (Extracted.textAddress + BitVec.ofNat 64 offset) len

def bBytes : List UInt8 :=
  [72, 184, 52, 72, 135, 4, 29, 6, 48, 220, 72, 137, 68, 36, 40, 72, 184, 214, 46, 33, 247, 171, 32, 162, 229, 72, 137, 68, 36, 32, 72, 184, 144, 48, 132, 120, 205, 5, 240, 172, 72, 137, 68, 36, 24, 72, 184, 223, 189, 196, 41, 98, 223, 156, 216, 72, 137, 68, 36, 16]

def bEffect (s : RamState) : Effect :=
  { rip := 0x110b42
    writes := [⟨(.reg 0 : Operand 64), 0xd89cdf6229c4bddf⟩,
      ⟨(.mem (stackPtr s + 40) : Operand 64), 0xdc30061d04874834⟩,
      ⟨(.mem (stackPtr s + 32) : Operand 64), 0xe5a220abf7212ed6⟩,
      ⟨(.mem (stackPtr s + 24) : Operand 64), 0xacf005cd78843090⟩,
      ⟨(.mem (stackPtr s + 16) : Operand 64), 0xd89cdf6229c4bddf⟩] }

theorem store_b [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary BPre (codeRange 0x110b06 bBytes) (Effect.post bEffect) := by
  advance_begin (mov_r64_imm64_effect_step 0x110b06 0x48 0xb8 (by simp [RexWPrefix]) (by decide) 0xdc30061d04874834)
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0x10b10 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x110b10 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110b06 bBytes 10 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.writable 40 (by simp)
    · x86_norm [stackPtr]
      exact hP.codeApart 40 (by simp) 0x10b10 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hP.codeApart 40 (by simp) 0x10b06 60 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x10b15 (by decide))
  advance_then (mov_r64_imm64_effect_step 0x110b15 0x48 0xb8 (by simp [RexWPrefix]) (by decide) 0xe5a220abf7212ed6)
  case sub => exact codeRange_slice_subset 0x110b06 bBytes 15 10
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x10b1f (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x110b1f 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110b06 bBytes 25 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.writable 32 (by simp)
    · x86_norm [stackPtr]
      exact hP.codeApart 32 (by simp) 0x10b1f 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hP.codeApart 32 (by simp) 0x10b06 60 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x10b24 (by decide))
  advance_then (mov_r64_imm64_effect_step 0x110b24 0x48 0xb8 (by simp [RexWPrefix]) (by decide) 0xacf005cd78843090)
  case sub => exact codeRange_slice_subset 0x110b06 bBytes 30 10
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x10b2e (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x110b2e 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110b06 bBytes 40 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.writable 24 (by simp)
    · x86_norm [stackPtr]
      exact hP.codeApart 24 (by simp) 0x10b2e 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hP.codeApart 24 (by simp) 0x10b06 60 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x10b33 (by decide))
  advance_then (mov_r64_imm64_effect_step 0x110b33 0x48 0xb8 (by simp [RexWPrefix]) (by decide) 0xd89cdf6229c4bddf)
  case sub => exact codeRange_slice_subset 0x110b06 bBytes 45 10
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x10b3d (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x110b3d 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110b06 bBytes 55 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.writable 16 (by simp)
    · x86_norm [stackPtr]
      exact hP.codeApart 16 (by simp) 0x10b3d 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hP.codeApart 16 (by simp) 0x10b06 60 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x10b42 (by decide))
  advance_finish [bEffect, stackPtr, Operand.read_reg64]

end P256.Proofs.Sec1.Affine.Uncompressed.Curve
