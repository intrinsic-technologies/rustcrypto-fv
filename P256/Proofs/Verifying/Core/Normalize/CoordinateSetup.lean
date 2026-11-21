import P256.Proofs.Verifying.Core.Normalize.InverseSetup

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Normalize.Coordinates

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program
open P256.Proofs.Common.Field (AdvanceTriple)

def xSetupBytes : List UInt8 :=
  [0x4c,0x8d,0xbc,0x24,0x40,0x2,0x0,0x0,0x48,0x8d,0xb4,0x24,0x80,0x0,0x0,0x0,0x4c,0x89,0xff,0x4c,0x89,0xf2]

def xSetupEffect (s : RamState) : Effect :=
  { rip := 0x10def3
    writes := [⟨(.reg 15 : Operand 64), stackPtr s + 576⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 576⟩,
      ⟨(.reg 6 : Operand 64), stackPtr s + 128⟩,
      ⟨(.reg 2 : Operand 64), (.reg 14 : Operand 64).read s⟩] }

theorem x_setup_block [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10dedd)
      (codeRange 0x10dedd xSetupBytes) (Effect.post xSetupEffect) := by
  advance_begin (lea_r64_effect_step 0x10dedd 0x4c (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 576)) (by decide +kernel) rfl rfl)
  case next =>
    intro _ _
    exact boundary_ne_program hout (inProgram_of_textOffset 0xdee5 (by decide))
  advance_then (lea_r64_effect_step 0x10dee5 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 128)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dedd xSetupBytes 8 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xdeed (by decide))
  advance_then (mov_r64_r64_effect_step 0x10deed 0x4c 0xff (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10dedd xSetupBytes 16 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xdef0 (by decide))
  advance_then (mov_r64_r64_effect_step 0x10def0 0x4c 0xf2 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10dedd xSetupBytes 19 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xdef3 (by decide))
  advance_finish [xSetupEffect]

theorem x_setup [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Core.Pre s boundary)
    (frame : Frame s t) (rip : t.RIP = 0x10dedd) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧
      (xSetupEffect t).Holds t u ∧ u.external = t.external := by
  obtain ⟨fuel, u, run, ready, _, effect⟩ := x_setup_block boundary pre.outerBoundary
    t (readyToStep frame.machine frame.bindingsSupported)
    (programText_slice (programLoaded_codeIn frame.loaded) 0xdedd xSetupBytes
      (by decide) (by decide +kernel)) rip
  have noMemory : ∀ c ∈ (xSetupEffect t).components, ∀ a, ¬ c.Covers a := by
    simp [xSetupEffect, Effect.components, Component.Covers]
  refine ⟨fuel, u, run, ?_, effect, effect.agrees.external noMemory⟩
  exact frame.after_registers ready effect.agrees noMemory
    (by simp [xSetupEffect, Effect.components])

def ySetupBytes : List UInt8 :=
  [0x48,0x8d,0xbc,0x24,0x88,0x1,0x0,0x0,0x48,0x8d,0xb4,0x24,0x80,0x0,0x0,0x0,0x4c,0x89,0xf2]

def ySetupEffect (s : RamState) : Effect :=
  { rip := 0x10df3f
    writes := [⟨(.reg 7 : Operand 64), stackPtr s + 392⟩,
      ⟨(.reg 6 : Operand 64), stackPtr s + 128⟩,
      ⟨(.reg 2 : Operand 64), (.reg 14 : Operand 64).read s⟩] }

theorem y_setup_block [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10df2c)
      (codeRange 0x10df2c ySetupBytes) (Effect.post ySetupEffect) := by
  advance_begin (lea_r64_effect_step 0x10df2c 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 392)) (by decide +kernel) rfl rfl)
  case next =>
    intro _ _
    exact boundary_ne_program hout (inProgram_of_textOffset 0xdf34 (by decide))
  advance_then (lea_r64_effect_step 0x10df34 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 128)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10df2c ySetupBytes 8 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xdf3c (by decide))
  advance_then (mov_r64_r64_effect_step 0x10df3c 0x4c 0xf2 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10df2c ySetupBytes 16 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xdf3f (by decide))
  advance_finish [ySetupEffect]

theorem y_setup [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Core.Pre s boundary)
    (frame : Frame s t) (rip : t.RIP = 0x10df2c) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧
      (ySetupEffect t).Holds t u ∧ u.external = t.external := by
  obtain ⟨fuel, u, run, ready, _, effect⟩ := y_setup_block boundary pre.outerBoundary
    t (readyToStep frame.machine frame.bindingsSupported)
    (programText_slice (programLoaded_codeIn frame.loaded) 0xdf2c ySetupBytes
      (by decide) (by decide +kernel)) rip
  have noMemory : ∀ c ∈ (ySetupEffect t).components, ∀ a, ¬ c.Covers a := by
    simp [ySetupEffect, Effect.components, Component.Covers]
  refine ⟨fuel, u, run, ?_, effect, effect.agrees.external noMemory⟩
  exact frame.after_registers ready effect.agrees noMemory
    (by simp [ySetupEffect, Effect.components])

end P256.Proofs.Verifying.Core.Normalize.Coordinates
