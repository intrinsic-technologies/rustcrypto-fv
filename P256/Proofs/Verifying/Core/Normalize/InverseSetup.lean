import P256.Proofs.Verifying.Core.Interface
import P256.Proofs.Program.Code
import P256.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Normalize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program
open P256.Proofs.Common.Field (AdvanceTriple)

def inverseSetupBytes : List UInt8 :=
  [0x48,0x8d,0x74,0x24,0x40,0x4c,0x8d,0xbc,0x24,0x80,0x3,0x0,0x0,0x4c,0x89,0xff]

def inverseSetupEffect (s : RamState) : Effect :=
  { rip := 0x10de51
    writes := [⟨(Operand.reg 6 : Operand 64), stackPtr s + 64⟩,
      ⟨(Operand.reg 15 : Operand 64), stackPtr s + 896⟩,
      ⟨(Operand.reg 7 : Operand 64), stackPtr s + 896⟩] }

theorem inverse_setup_block [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10de41)
      (codeRange 0x10de41 inverseSetupBytes) (Effect.post inverseSetupEffect) := by
  advance_begin (lea_r64_effect_step 0x10de41 0x48 (by simp [RexWPrefix])
    6 (.sib 4 none 0 (.d8 64)) (by decide +kernel) rfl rfl)
  case next =>
    intro _ _
    exact boundary_ne_program hout (inProgram_of_textOffset 0xde46 (by decide))
  advance_then (lea_r64_effect_step 0x10de46 0x4c (by simp [RexWPrefix])
    7 (.sib 4 none 0 (.d32 896)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10de41 inverseSetupBytes 5 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xde4e (by decide))
  advance_then (mov_r64_r64_effect_step 0x10de4e 0x4c 0xff (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10de41 inverseSetupBytes 13 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xde51 (by decide))
  advance_finish [inverseSetupEffect]

theorem inverse_setup [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Core.Pre s boundary) (frame : Frame s t) (rip : t.RIP = 0x10de41) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧
      (inverseSetupEffect t).Holds t u ∧ u.external = t.external := by
  obtain ⟨fuel, u, run, ready, _, effect⟩ := inverse_setup_block boundary pre.outerBoundary
    t (readyToStep frame.machine frame.bindingsSupported)
    (programText_slice (programLoaded_codeIn frame.loaded) 0xde41 inverseSetupBytes
      (by decide) (by decide +kernel)) rip
  have noMemory : ∀ c ∈ (inverseSetupEffect t).components, ∀ a, ¬ c.Covers a := by
    simp [inverseSetupEffect, Effect.components, Component.Covers]
  refine ⟨fuel, u, run, ?_, effect, effect.agrees.external noMemory⟩
  exact frame.after_registers ready effect.agrees noMemory
    (by simp [inverseSetupEffect, Effect.components])

end P256.Proofs.Verifying.Core.Normalize
