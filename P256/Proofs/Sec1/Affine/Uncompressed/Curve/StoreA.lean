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

structure APre (s : RamState) : Prop where
  rip : s.RIP = 0x110aa8
  writable : ∀ off ∈ ([16,24,32,40] : List (BitVec 64)),
    P256.Proofs.Common.Instructions.CrossPageStore.Writable s (stackPtr s + off) 8
  codeApart : ∀ off ∈ ([16,24,32,40] : List (BitVec 64)), ∀ offset len : Nat,
    offset + len ≤ 118431 → RangeApart (stackPtr s + off) 8
      (Extracted.textAddress + BitVec.ofNat 64 offset) len

def aBytes : List UInt8 :=
  [72, 184, 4, 0, 0, 0, 252, 255, 255, 255, 72, 137, 68, 36, 40, 72, 184, 255, 255, 255, 255, 3, 0, 0, 0, 72, 137, 68, 36, 24, 72, 199, 68, 36, 32, 0, 0, 0, 0, 72, 199, 68, 36, 16, 252, 255, 255, 255]

def aEffect (s : RamState) : Effect :=
  { rip := 0x110ad8
    writes := [⟨(.reg 0 : Operand 64), 0x3ffffffff⟩,
      ⟨(.mem (stackPtr s + 40) : Operand 64), 0xfffffffc00000004⟩,
      ⟨(.mem (stackPtr s + 24) : Operand 64), 0x3ffffffff⟩,
      ⟨(.mem (stackPtr s + 32) : Operand 64), 0x0⟩,
      ⟨(.mem (stackPtr s + 16) : Operand 64), 0xfffffffffffffffc⟩] }

theorem store_a [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary APre (codeRange 0x110aa8 aBytes) (Effect.post aEffect) := by
  advance_begin (mov_r64_imm64_effect_step 0x110aa8 0x48 0xb8 (by simp [RexWPrefix]) (by decide) 0xfffffffc00000004)
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0x10ab2 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x110ab2 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110aa8 aBytes 10 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.writable 40 (by simp)
    · x86_norm [stackPtr]
      exact hP.codeApart 40 (by simp) 0x10ab2 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hP.codeApart 40 (by simp) 0x10aa8 48 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x10ab7 (by decide))
  advance_then (mov_r64_imm64_effect_step 0x110ab7 0x48 0xb8 (by simp [RexWPrefix]) (by decide) 0x3ffffffff)
  case sub => exact codeRange_slice_subset 0x110aa8 aBytes 15 10
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x10ac1 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x110ac1 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110aa8 aBytes 25 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.writable 24 (by simp)
    · x86_norm [stackPtr]
      exact hP.codeApart 24 (by simp) 0x10ac1 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hP.codeApart 24 (by simp) 0x10aa8 48 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x10ac6 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x110ac6 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl 0x0)
  case sub => exact codeRange_slice_subset 0x110aa8 aBytes 30 9
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.writable 32 (by simp)
    · x86_norm [stackPtr]
      exact hP.codeApart 32 (by simp) 0x10ac6 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hP.codeApart 32 (by simp) 0x10aa8 48 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x10acf (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x110acf 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl 0xfffffffc)
  case sub => exact codeRange_slice_subset 0x110aa8 aBytes 39 9
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.writable 16 (by simp)
    · x86_norm [stackPtr]
      exact hP.codeApart 16 (by simp) 0x10acf 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hP.codeApart 16 (by simp) 0x10aa8 48 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x10ad8 (by decide))
  advance_finish [aEffect, stackPtr, Operand.read_reg64]

end P256.Proofs.Sec1.Affine.Uncompressed.Curve
