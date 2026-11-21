import P256.Proofs.Verifying.Core.Interface
import P256.Proofs.Program.Code
import P256.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Scalars

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program
open P256.Proofs.Common.Field (AdvanceTriple)

def inverseSetupBytes : List UInt8 :=
  [0x48, 0x8d, 0xbc, 0x24, 0x80, 0x0, 0x0, 0x0, 0x48, 0x8d, 0xb4, 0x24, 0xe0, 0x2, 0x0, 0x0]

def inverseSetupEffect (s : RamState) : Effect :=
  { rip := 0x10dc88
    writes := [⟨(Operand.reg 7 : Operand 64), rspOf s + 128⟩,
      ⟨(Operand.reg 6 : Operand 64), rspOf s + 736⟩] }

theorem inverse_setup_block [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10dc78)
      (codeRange 0x10dc78 inverseSetupBytes) (Effect.post inverseSetupEffect) := by
  advance_begin (lea_r64_effect_step 0x10dc78 0x48 (by simp [RexWPrefix])
    7 (.sib 4 none 0 (.d32 128)) (by decide +kernel) rfl rfl)
  case next =>
    intro _ _
    exact boundary_ne_program hout (inProgram_of_textOffset 0xdc80 (by decide))
  advance_then (lea_r64_effect_step 0x10dc80 0x48 (by simp [RexWPrefix])
    6 (.sib 4 none 0 (.d32 736)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dc78 inverseSetupBytes 8 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xdc88 (by decide))
  advance_finish [inverseSetupEffect]

theorem inverse_setup [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Core.Pre s boundary)
    (frame : Frame s t) (rip : t.RIP = 0x10dc78) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧
      (inverseSetupEffect t).Holds t u ∧ u.external = t.external := by
  obtain ⟨fuel, u, run, ready, _, effect⟩ := inverse_setup_block boundary pre.outerBoundary
    t (readyToStep frame.machine frame.bindingsSupported)
    (programText_slice (programLoaded_codeIn frame.loaded) 0xdc78 inverseSetupBytes
      (by decide) (by decide +kernel)) rip
  have noMemory : ∀ c ∈ (inverseSetupEffect t).components, ∀ a, ¬ c.Covers a := by
    simp [inverseSetupEffect, Effect.components, Component.Covers]
  refine ⟨fuel, u, run, ?_, effect, effect.agrees.external noMemory⟩
  exact frame.after_registers ready effect.agrees
    (fun c hc a ha => (noMemory c hc a ha).elim)
    (by simp [inverseSetupEffect, Effect.components])


end P256.Proofs.Verifying.Core.Scalars
