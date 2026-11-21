import P256.Proofs.Verifying.Core.Normalize.InverseSetup

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Finish.CanonicalSetup

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program
open P256.Proofs.Common.Field (AdvanceTriple)

def setupBytes : List UInt8 :=
  [0x48,0x8d,0xbc,0x24,0x80,0x0,0x0,0x0,0x48,0x8d,0x9c,0x24,0x40,0x2,0x0,0x0,0x48,0x89,0xde]

def setupEffect (s : RamState) : Effect :=
  { rip := 0x10e047
    writes := [⟨(.reg 7 : Operand 64), stackPtr s + 128⟩,
      ⟨(.reg 3 : Operand 64), stackPtr s + 576⟩,
      ⟨(.reg 6 : Operand 64), stackPtr s + 576⟩] }

theorem setup_block [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10e034)
      (codeRange 0x10e034 setupBytes) (Effect.post setupEffect) := by
  advance_begin (lea_r64_effect_step 0x10e034 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 128)) (by decide +kernel) rfl rfl)
  case next =>
    intro _ _
    exact boundary_ne_program hout (inProgram_of_textOffset 0xe03c (by decide))
  advance_then (lea_r64_effect_step 0x10e03c 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d32 576)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10e034 setupBytes 8 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xe044 (by decide))
  advance_then (mov_r64_r64_effect_step 0x10e044 0x48 0xde (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10e034 setupBytes 16 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xe047 (by decide))
  advance_finish [setupEffect]

theorem setup [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Core.Pre s boundary)
    (frame : Frame s t) (rip : t.RIP = 0x10e034) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧
      (setupEffect t).Holds t u ∧ u.external = t.external := by
  obtain ⟨fuel, u, run, ready, _, effect⟩ := setup_block boundary pre.outerBoundary
    t (readyToStep frame.machine frame.bindingsSupported)
    (programText_slice (programLoaded_codeIn frame.loaded) 0xe034 setupBytes
      (by decide) (by decide +kernel)) rip
  have noMemory : ∀ c ∈ (setupEffect t).components, ∀ a, ¬ c.Covers a := by
    simp [setupEffect, Effect.components, Component.Covers]
  refine ⟨fuel, u, run, ?_, effect, effect.agrees.external noMemory⟩
  exact frame.after_registers ready effect.agrees noMemory
    (by simp [setupEffect, Effect.components])

end P256.Proofs.Verifying.Core.Finish.CanonicalSetup
