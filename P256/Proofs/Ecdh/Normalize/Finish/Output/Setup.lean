import P256.Proofs.Ecdh.Normalize.State
import P256.Proofs.Program.Code
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false
open P256.Proofs.Common.Field (AdvanceTriple)
namespace P256.Proofs.Ecdh.Normalize.Finish.Output
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

def setupBytes : List UInt8 := [72, 141, 188, 36, 248, 3, 0, 0, 72, 141, 180, 36, 248, 0, 0, 0]

def setupEffect (s : RamState) : Effect :=
  { rip := 0x10052a
    writes := [⟨(Operand.reg 7 : Operand 64), stackPtr s + 1016⟩,
      ⟨(Operand.reg 6 : Operand 64), stackPtr s + 248⟩] }

theorem setup_registers [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10051a)
      (codeRange 0x10051a setupBytes) (Effect.post setupEffect) := by
  advance_begin (lea_r64_effect_step 0x10051a 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 1016)) (by decide +kernel) rfl rfl)
  case next =>
    intro _ _
    exact boundary_ne_program hout (inProgram_of_textOffset 0x522 (by decide))
  advance_then (lea_r64_effect_step 0x100522 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 248)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10051a setupBytes 8 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x52a (by decide))
  advance_finish [setupEffect]

theorem setup [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (state : FrameState s t 32 3464 2056) (hout : ¬ InProgram boundary.rip)
    (rip : t.RIP = 0x10051a) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 32 3464 2056 ∧
      (setupEffect t).Holds t u ∧ u.external = t.external := by
  obtain ⟨fuel,u,run,ready,_,effect⟩ := setup_registers boundary hout t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x51a setupBytes
      (by decide) (by decide +kernel)) rip
  have hm : ∀ c ∈ (setupEffect t).components, ∀ a, ¬ c.Covers a := by
    simp [setupEffect, Effect.components, Component.Covers]
  exact ⟨fuel,u,run,state.after_registers ready effect.agrees hm
    (by simp [setupEffect, Effect.components]),effect,effect.agrees.external hm⟩

end P256.Proofs.Ecdh.Normalize.Finish.Output
