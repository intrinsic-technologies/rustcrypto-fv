import P256.Proofs.Scalar.Multiply.Interface
import P256.Proofs.Field.Montgomery.Prologue
import P256.Proofs.Program.Push
import P256.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Sub.Generated.Imm32.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Scalar.Multiply

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

open P256.Proofs.Field.Montgomery (SavedEntry saveComponents)

set_option hygiene false in
macro "scalar_multiply_save" pre:term:max : tactic =>
  `(tactic| (
  obtain ⟨u, run, ready, loaded, rip, rsp, frame, memory⟩ :=
    push_exists ($pre).stack (($pre).avoids _ (by simp)) ($pre).outerBoundary
      (readyToStep ($pre).machine ($pre).bindingsSupported) ($pre).loaded (fun _ h => h)
      3 0 0x13040 (by simp only [BitVec.sub_zero]) ($pre).rip
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  obtain ⟨t, step, readyt, effect⟩ :=
    sub_r64_imm32_effect_step 0x113041 0x48 0xec 128
      (by unfold RexWPrefix; decide +kernel) rfl rfl u ready
      (programText_slice (programLoaded_codeIn loaded) 0x13041
        [0x48,0x81,0xec,0x80,0,0,0] (by decide +kernel) (by decide +kernel)) rip
  have hip : t.RIP = 0x113048 := effect.rip
  have run2 : Advances boundary 1 u t := Advances.of_step step (.inl (by
    rw [hip]
    exact boundary_ne_program ($pre).outerBoundary
      (inProgram_of_textOffset 0x13048 (by decide +kernel))))
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

theorem save_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : MultiplyPre s boundary) : ∃ t, SavedEntry s t boundary 0x113048 := by
  scalar_multiply_save pre

def argumentBytes : List UInt8 :=
  [0x48,0x89,0xd1,0x48,0x89,0xfb,0x48,0x8d,0x7c,0x24,0x40,
   0xba,4,0,0,0,0x41,0xb8,4,0,0,0]

def argumentEffect (s : RamState) : Effect :=
  { rip := 0x11305e
    writes := [⟨(.reg 1 : Operand 64), s.regValue .rdx⟩,
      ⟨(.reg 3 : Operand 64), s.regValue .rdi⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 64⟩,
      ⟨(.reg 2 : Operand 64), 4⟩, ⟨(.reg 8 : Operand 64), 4⟩] }

theorem arguments [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x113048) (codeRange 0x113048 argumentBytes)
      (Effect.post argumentEffect) := by
  advance_begin (mov_r64_r64_effect_step 0x113048 0x48 0xd1
    (by simp [RexWPrefix]) rfl)
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0x1304b (by decide))
  advance_then (mov_r64_r64_effect_step 0x11304b 0x48 0xfb
    (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x113048 argumentBytes 3 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1304e (by decide))
  advance_then (lea_r64_effect_step 0x11304e 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d8 64)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113048 argumentBytes 6 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13053 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x113053 0xba (by decide +kernel) 4)
  case sub => exact codeRange_slice_subset 0x113048 argumentBytes 11 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13058 (by decide))
  advance_then (mov_r32_imm32_rex_effect_step 0x113058 0x41 0xb8
    (by simp [RexNoWPrefix]) (by decide +kernel) 4)
  case sub => exact codeRange_slice_subset 0x113048 argumentBytes 16 6
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1305e (by decide))
  advance_finish [argumentEffect, stackPtr, Operand.read_reg64]

end P256.Proofs.Scalar.Multiply
