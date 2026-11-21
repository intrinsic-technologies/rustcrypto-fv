import P256.Proofs.Ecdh.Normalize.State
import P256.Proofs.Program.Code
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)
namespace P256.Proofs.Ecdh.Normalize
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

def inverseSetupBytes : List UInt8 :=
  [72, 141, 180, 36, 216, 0, 0, 0, 76, 141, 124, 36, 80, 76, 137, 255]

def inverseSetupEffect (s : RamState) : Effect :=
  { rip := 0x100350
    writes := [⟨(Operand.reg 6 : Operand 64), stackPtr s + 216⟩,
      ⟨(Operand.reg 15 : Operand 64), stackPtr s + 80⟩,
      ⟨(Operand.reg 7 : Operand 64), stackPtr s + 80⟩] }

theorem inverse_setup_block [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x100340)
      (codeRange 0x100340 inverseSetupBytes) (Effect.post inverseSetupEffect) := by
  advance_begin (lea_r64_effect_step 0x100340 0x48 (by simp [RexWPrefix])
    6 (.sib 4 none 0 (.d32 216)) (by decide +kernel) rfl rfl)
  case next =>
    intro _ _
    exact boundary_ne_program hout (inProgram_of_textOffset 0x348 (by decide))
  advance_then (lea_r64_effect_step 0x100348 0x4c (by simp [RexWPrefix])
    7 (.sib 4 none 0 (.d8 80)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100340 inverseSetupBytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x34d (by decide))
  advance_then (mov_r64_r64_effect_step 0x10034d 0x4c 0xff (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x100340 inverseSetupBytes 13 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x350 (by decide))
  advance_finish [inverseSetupEffect]

theorem inverse_setup [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x100000 32 32 3464)
    (state : FrameState s t 32 3464 2056) (rip : t.RIP = 0x100340) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 32 3464 2056 ∧
      (inverseSetupEffect t).Holds t u ∧ u.external = t.external := by
  obtain ⟨fuel,u,run,ready,_,effect⟩ := inverse_setup_block boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x340 inverseSetupBytes
      (by decide) (by decide +kernel)) rip
  have hm : ∀ c ∈ (inverseSetupEffect t).components, ∀ a, ¬ c.Covers a := by
    simp [inverseSetupEffect, Effect.components, Component.Covers]
  exact ⟨fuel,u,run,state.after_registers ready effect.agrees hm
    (by simp [inverseSetupEffect, Effect.components]),effect,effect.agrees.external hm⟩

end P256.Proofs.Ecdh.Normalize
