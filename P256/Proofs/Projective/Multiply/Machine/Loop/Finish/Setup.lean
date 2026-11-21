import P256.Proofs.Projective.Multiply.Machine.Loop.Initial.Setup
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Memory

set_option autoImplicit false

open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Projective.Multiply.Machine.Loop

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs

structure FinishPre (s : RamState) : Prop where
  rip : s.RIP = 0x103425
  readable : MemReadable s (stackPtr s + 16) 8

def finishBytes : List UInt8 :=
  [0x48,0x8d,0x74,0x24,0x28,0xb9,0x0c,0,0,0,0x48,0x8b,0x44,0x24,0x10,0x48,0x89,0xc7]

def finishEffect (s : RamState) : Effect :=
  { rip := 0x103437
    writes := [⟨(Operand.reg 6 : Operand 64), stackPtr s + 40⟩,
      ⟨(Operand.reg 1 : Operand 64), 12⟩,
      ⟨(Operand.reg 0 : Operand 64), (Operand.mem (stackPtr s + 16) : Operand 64).read s⟩,
      ⟨(Operand.reg 7 : Operand 64), (Operand.mem (stackPtr s + 16) : Operand 64).read s⟩] }

theorem finish_setup [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    P256.Proofs.Common.Field.AdvanceTriple boundary FinishPre (codeRange 0x103425 finishBytes)
      (Effect.post finishEffect) := by
  advance_begin (lea_r64_effect_step 0x103425 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x342a (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10342a 0xb9 (by decide) 12)
  case sub => exact codeRange_slice_subset 0x103425 finishBytes 5 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x342f (by decide))⟩
  advance_then (mov_r64_m64_effect_step 0x10342f 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x103425 finishBytes 10 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x3434 (by decide))⟩
    x86_norm
    exact hP.readable
  advance_then (mov_r64_r64_effect_step 0x103434 0x48 0xc7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x103425 finishBytes 15 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x3437 (by decide))⟩
  apply P256.Proofs.Common.Field.AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [finishEffect]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [finishEffect]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [finishEffect]
  · x86_norm [finishEffect]
    all_goals (repeat first | constructor | rfl)

end P256.Proofs.Projective.Multiply.Machine.Loop
