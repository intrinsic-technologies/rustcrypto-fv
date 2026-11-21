import P256.Proofs.Ecdh.Normalize.State
import P256.Proofs.Program.Code
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false
open P256.Proofs.Common.Field (AdvanceTriple)
namespace P256.Proofs.Ecdh.Normalize.Coordinates
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

def xBytes : List UInt8 := [76, 141, 188, 36, 248, 0, 0, 0, 72, 141, 180, 36, 248, 3, 0, 0, 76, 137, 255, 76, 137, 242]

def xEffect (s : RamState) : Effect :=
  { rip := 0x1003ed
    writes := [⟨(Operand.reg 15 : Operand 64), stackPtr s + 248⟩,
      ⟨(Operand.reg 6 : Operand 64), stackPtr s + 1016⟩,
      ⟨(Operand.reg 7 : Operand 64), stackPtr s + 248⟩,
      ⟨(Operand.reg 2 : Operand 64), s.regValue .r14⟩] }

theorem x_registers [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1003d7)
      (codeRange 0x1003d7 xBytes) (Effect.post xEffect) := by
  advance_begin (lea_r64_effect_step 0x1003d7 0x4c (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 248)) (by decide +kernel) rfl rfl)
  case next =>
    intro _ _
    exact boundary_ne_program hout (inProgram_of_textOffset 0x3df (by decide))
  advance_then (lea_r64_effect_step 0x1003df 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 1016)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1003d7 xBytes 8 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x3e7 (by decide))
  advance_then (mov_r64_r64_effect_step 0x1003e7 0x4c 0xff (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1003d7 xBytes 16 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x3ea (by decide))
  advance_then (mov_r64_r64_effect_step 0x1003ea 0x4c 0xf2 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1003d7 xBytes 19 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x3ed (by decide))
  advance_finish [xEffect]

theorem x_setup [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (state : FrameState s t 32 3464 2056) (hout : ¬ InProgram boundary.rip)
    (rip : t.RIP = 0x1003d7) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 32 3464 2056 ∧
      (xEffect t).Holds t u ∧ u.external = t.external := by
  obtain ⟨fuel,u,run,ready,_,effect⟩ := x_registers boundary hout t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x3d7 xBytes
      (by decide) (by decide +kernel)) rip
  have hm : ∀ c ∈ (xEffect t).components, ∀ a, ¬ c.Covers a := by
    simp [xEffect, Effect.components, Component.Covers]
  exact ⟨fuel,u,run,state.after_registers ready effect.agrees hm
    (by simp [xEffect, Effect.components]),effect,effect.agrees.external hm⟩

def yBytes : List UInt8 := [72, 141, 124, 36, 48, 72, 141, 180, 36, 248, 3, 0, 0, 76, 137, 242]

def yEffect (s : RamState) : Effect :=
  { rip := 0x100442
    writes := [⟨(Operand.reg 7 : Operand 64), stackPtr s + 48⟩,
      ⟨(Operand.reg 6 : Operand 64), stackPtr s + 1016⟩,
      ⟨(Operand.reg 2 : Operand 64), s.regValue .r14⟩] }

theorem y_registers [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x100432)
      (codeRange 0x100432 yBytes) (Effect.post yEffect) := by
  advance_begin (lea_r64_effect_step 0x100432 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 48)) (by decide +kernel) rfl rfl)
  case next =>
    intro _ _
    exact boundary_ne_program hout (inProgram_of_textOffset 0x437 (by decide))
  advance_then (lea_r64_effect_step 0x100437 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 1016)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100432 yBytes 5 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x43f (by decide))
  advance_then (mov_r64_r64_effect_step 0x10043f 0x4c 0xf2 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x100432 yBytes 13 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x442 (by decide))
  advance_finish [yEffect]

theorem y_setup [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (state : FrameState s t 32 3464 2056) (hout : ¬ InProgram boundary.rip)
    (rip : t.RIP = 0x100432) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 32 3464 2056 ∧
      (yEffect t).Holds t u ∧ u.external = t.external := by
  obtain ⟨fuel,u,run,ready,_,effect⟩ := y_registers boundary hout t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x432 yBytes
      (by decide) (by decide +kernel)) rip
  have hm : ∀ c ∈ (yEffect t).components, ∀ a, ¬ c.Covers a := by
    simp [yEffect, Effect.components, Component.Covers]
  exact ⟨fuel,u,run,state.after_registers ready effect.agrees hm
    (by simp [yEffect, Effect.components]),effect,effect.agrees.external hm⟩

end P256.Proofs.Ecdh.Normalize.Coordinates
