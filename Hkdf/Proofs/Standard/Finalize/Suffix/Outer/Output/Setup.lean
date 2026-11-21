import Hkdf.Proofs.Standard.Finalize.Suffix.State
import Hkdf.Proofs.Common.CallFrame.Stack
import Hkdf.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Output.Setup

open Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.Field (AdvanceTriple)

private def bytes : List UInt8 :=
  [0x48,0x8d,0x7c,0x24,0x48,0x48,0x8d,0xb4,0x24,0xd8,0,0,0,0xba,0x20,0,0,0]

private def effect (s : RamState) : Effect :=
  { rip := 0x10e0bb
    writes := [⟨(.reg 7 : Operand 64), rspOf s + 72⟩,
      ⟨(.reg 6 : Operand 64), rspOf s + 216⟩,
      ⟨(.reg 2 : Operand 64), 32⟩] }

private theorem execute [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s ↦ s.RIP = 0x10e0a9)
      (codeRange 0x10e0a9 bytes) (Effect.post effect) := by
  advance_begin (lea_r64_effect_step 0x10e0a9 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d8 72)) (by decide) rfl rfl)
  case next => exact fun _ _ ↦ boundary_ne_program outside (inProgram_of_textOffset 0xe0ae (by decide))
  advance_then (lea_r64_effect_step 0x10e0ae 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d32 216)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10e0a9 bytes 5 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xe0b6 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10e0b6 0xba (by decide) 32)
  case sub => exact codeRange_slice_subset 0x10e0a9 bytes 13 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xe0bb (by decide))
  advance_finish [effect]

theorem run [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre initial boundary 0x10dd90 144 176 1264)
    (state : Suffix.State initial boundary s) (rip : s.RIP = 0x10e0a9) :
    ∃ t, Suffix.State initial boundary t ∧ t.RIP = 0x10e0bb ∧
      t.regValue .rdi = stackPtr initial - 336 ∧
      t.regValue .rsi = stackPtr initial - 192 ∧
      t.regValue .rdx = 32 ∧ t.external = s.external := by
  obtain ⟨fuel, t, execution, ready, _, result⟩ := execute boundary pre.outerBoundary s
    (Hkdf.Proofs.Common.Machine.supportedMachine_readyToStep state.running.machine)
    (programText_slice (programLoaded_codeIn state.running.loaded) 0xe0a9 bytes
      (by decide) (by decide +kernel)) rip
  have frame : AgreesExcept [.reg 7, .reg 6, .reg 2, .rip] s t := by
    simpa only [effect, Effect.components, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Write.component, Operand.component] using result.agrees
  have memory : t.external = s.external := frame.external (by
    intro c hc a
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl <;> exact fun h ↦ h)
  have stable : Suffix.State initial boundary t := state.of_agrees pre execution ready frame
    (by
      intro c hc a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl <;> exact ha.elim)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false];
        intro c hc; rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
    (by intro i hi; rw [memory])
  have stores := result.writes
  change t.regValue .rdi = stackPtr s + 72 ∧
    t.regValue .rsi = stackPtr s + 216 ∧ t.regValue .rdx = 32 at stores
  refine ⟨t, stable, result.rip, ?_, ?_, stores.2.2, memory⟩
  · rw [stores.1, state.rsp]; bv_omega
  · rw [stores.2.1, state.rsp]; bv_omega

end Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Output.Setup
