import P256.Proofs.Field.Interface
import P256.Proofs.Program.Push
import P256.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Sub.Generated.Imm32.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Field.Montgomery

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

def saveComponents (s : RamState) : List Component :=
  [.reg 4, .flags, .rip, .mem (stackPtr s - 8) 8]

structure SavedEntry [Bindings] (initial s : RamState) (boundary : ReturnBoundary) (pc : BitVec 64 := 0x113898) : Prop where
  execution : Advances boundary 2 initial s
  ready : ReadyToStep s
  loaded : ProgramLoaded s
  rip : s.RIP = pc
  rsp : stackPtr s = stackPtr initial - 136
  memory : s.external = memStore initial.external (stackPtr initial - 8) (initial.regValue .rbx)
  agrees : AgreesExcept (saveComponents initial) initial s

set_option hygiene false in
macro "montgomery_save" square:term:max pre:term:max : tactic =>
  `(tactic| (
  obtain ⟨u, run, ready, loaded, rip, rsp, frame, memory⟩ :=
    push_exists ($pre).stack (($pre).avoids _ (by simp)) ($pre).outerBoundary
      (readyToStep ($pre).machine ($pre).bindingsSupported) ($pre).loaded (fun _ h => h)
      3 0 (if $square then 0x13800 else 0x13890) (by simp only [BitVec.sub_zero]) ($pre).rip
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  obtain ⟨t, step, readyt, effect⟩ :=
    sub_r64_imm32_effect_step (if $square then 0x113801 else 0x113891) 0x48 0xec 128
      (by unfold RexWPrefix; decide +kernel) rfl rfl u ready
      (programText_slice (programLoaded_codeIn loaded) (if $square then 0x13801 else 0x13891)
        [0x48,0x81,0xec,0x80,0,0,0] (by decide +kernel) (by decide +kernel)) rip
  have hip : t.RIP = (if $square then 0x113808 else 0x113898) := effect.rip
  have run2 : Advances boundary 1 u t := Advances.of_step step (.inl (by
    rw [hip]
    exact boundary_ne_program ($pre).outerBoundary
      (inProgram_of_textOffset (if $square then 0x13808 else 0x13898) (by decide +kernel))))
  have hm : t.external = u.external := effect.agrees.external
    (by simp [subR64Imm32Effect_components, Component.Covers])
  refine ⟨t, ⟨run.trans run2, readyt, ?_, hip, ?_, hm.trans memory, ?_⟩⟩
  · simpa only [ProgramLoaded, hm] using loaded
  · have hw : stackPtr t = stackPtr u - 128 := effect.writes
    rw [hw, rsp, BitVec.sub_sub]
    rfl
  · apply (frame.trans effect.agrees).mono
    simp only [saveComponents, subR64Imm32Effect_components, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false]
    intro c hc
    rcases hc with (rfl | rfl | rfl) | (rfl | rfl | rfl) <;>
      simp [gprNumber, rexB, modrmRm]
  ))

theorem save_correct_at (square : Bool) [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary (if square then 0x113800 else 0x113890) 32 32 280) : ∃ t, SavedEntry s t boundary (if square then 0x113808 else 0x113898) := by
  cases square
  · montgomery_save false pre
  · montgomery_save true pre

theorem save_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : MultiplyPre s boundary) : ∃ t, SavedEntry s t boundary := by
  exact save_correct_at false pre.toCalleePre

def argumentBytes : List UInt8 :=
  [0x48,0x89,0xd1,0x48,0x89,0xfb,0x48,0x8d,0x7c,0x24,0x40,
   0xba,4,0,0,0,0x41,0xb8,4,0,0,0]

def argumentEffect (s : RamState) : Effect :=
  { rip := 0x1138ae
    writes := [⟨(.reg 1 : Operand 64), s.regValue .rdx⟩,
      ⟨(.reg 3 : Operand 64), s.regValue .rdi⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 64⟩,
      ⟨(.reg 2 : Operand 64), 4⟩, ⟨(.reg 8 : Operand 64), 4⟩] }

theorem arguments [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x113898) (codeRange 0x113898 argumentBytes)
      (Effect.post argumentEffect) := by
  advance_begin (mov_r64_r64_effect_step 0x113898 0x48 0xd1
    (by simp [RexWPrefix]) rfl)
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0x1389b (by decide))
  advance_then (mov_r64_r64_effect_step 0x11389b 0x48 0xfb
    (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x113898 argumentBytes 3 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1389e (by decide))
  advance_then (lea_r64_effect_step 0x11389e 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d8 64)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113898 argumentBytes 6 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x138a3 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x1138a3 0xba (by decide +kernel) 4)
  case sub => exact codeRange_slice_subset 0x113898 argumentBytes 11 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x138a8 (by decide))
  advance_then (mov_r32_imm32_rex_effect_step 0x1138a8 0x41 0xb8
    (by simp [RexNoWPrefix]) (by decide +kernel) 4)
  case sub => exact codeRange_slice_subset 0x113898 argumentBytes 16 6
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x138ae (by decide))
  advance_finish [argumentEffect, stackPtr, Operand.read_reg64]

end P256.Proofs.Field.Montgomery
