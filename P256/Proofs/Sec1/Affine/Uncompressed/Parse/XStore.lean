import P256.Proofs.Program.Code
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Instructions.Bswap
import X86Proofs.Instructions.MovLoad.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Parse

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)
open P256.Proofs.Common.Instructions (bswap64 bswap_r64_effect_step)

structure xStorePre (s : RamState) : Prop where
  rip : s.RIP = 0x11083c
  writable : ∀ off ∈ ([168,176,184,192] : List (BitVec 64)),
    P256.Proofs.Common.Instructions.CrossPageStore.Writable s (stackPtr s + off) 8
  apart : ∀ off ∈ ([168,176,184,192] : List (BitVec 64)),
    RangeApart (stackPtr s + off) 8 0x11083c 32

def xStoreBytes : List UInt8 :=
  [72, 137, 148, 36, 168, 0, 0, 0, 72, 137, 180, 36, 176, 0, 0, 0, 72, 137, 140, 36, 184, 0, 0, 0, 72, 137, 132, 36, 192, 0, 0, 0]

def xStoreEffect (s : RamState) : Effect :=
  { rip := 0x11085c
    writes := [⟨(.mem (stackPtr s + 168) : Operand 64), (Operand.reg 2 : Operand 64).read s⟩,
      ⟨(.mem (stackPtr s + 176) : Operand 64), (Operand.reg 6 : Operand 64).read s⟩,
      ⟨(.mem (stackPtr s + 184) : Operand 64), (Operand.reg 1 : Operand 64).read s⟩,
      ⟨(.mem (stackPtr s + 192) : Operand 64), (Operand.reg 0 : Operand 64).read s⟩] }

theorem x_store [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary xStorePre (codeRange 0x11083c xStoreBytes)
      (Effect.post xStoreEffect) := by
  advance_begin (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any
    0x11083c 0x48 (by simp [RexWPrefix]) 2
    (.sib 4 none 0 (.d32 168)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    exact ⟨h.rip, h.writable 168 (by simp), h.apart 168 (by simp) |>.sub 0 8 (by decide)⟩
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm
    exact h.apart 168 (by simp)
  case next =>
    intro _ _
    exact boundary_ne_program outside (inProgram_of_textOffset 0x10844 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any
    0x110844 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d32 176)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11083c xStoreBytes 8 8
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.writable 176 (by simp)
    · x86_norm [stackPtr]
      exact (hP.apart 176 (by simp)).sub 8 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hP.apart 176 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1084c (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any
    0x11084c 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d32 184)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11083c xStoreBytes 16 8
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.writable 184 (by simp)
    · x86_norm [stackPtr]
      exact (hP.apart 184 (by simp)).sub 16 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hP.apart 184 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10854 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any
    0x110854 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 192)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11083c xStoreBytes 24 8
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.writable 192 (by simp)
    · x86_norm [stackPtr]
      exact (hP.apart 192 (by simp)).sub 24 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hP.apart 192 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1085c (by decide))
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [xStoreEffect, stackPtr, Operand.read_reg64]
    all_goals repeat first | constructor | rfl
  · x86_norm [xStoreEffect, stackPtr, Operand.read_reg64]
    all_goals repeat first | constructor | rfl
  · intro i; cases i <;> x86_norm [xStoreEffect, stackPtr, Operand.read_reg64]
    all_goals repeat first | constructor | rfl
  · x86_norm [xStoreEffect, stackPtr, Operand.read_reg64]
    all_goals repeat first | constructor | rfl

end P256.Proofs.Sec1.Affine.Uncompressed.Parse
