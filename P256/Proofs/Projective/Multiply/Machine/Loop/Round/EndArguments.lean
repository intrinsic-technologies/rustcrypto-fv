import P256.Proofs.Projective.Multiply.Machine.Loop.Initial.Setup
import P256.Proofs.Projective.Multiply.Machine.Loop.Round.AfterDouble
import X86Proofs.Instructions.Test.Generated.RR.Triple
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Projective.Multiply.Machine.Loop.Round

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs


attribute [local x86_compose] decR64Effect decSpec
attribute [local x86_local] dec_local

structure EndSetupPre (s : RamState) : Prop where
  rip : s.RIP = 0x1033ce
  table : MemReadable s (stackPtr s + 24) 8
  cursor : MemReadable s (stackPtr s + 8) 8
  remaining : MemReadable s (stackPtr s + 32) 8

def endSetupBytes : List UInt8 :=
  [0x4c,0x8b,0x4c,0x24,0x08,0x49,0xff,0xc9,0x4c,0x8b,0x7c,0x24,0x20,0x4d,0x85,0xff,0x48,0x8b,0x5c,0x24,0x18]

def endSetupEffect (s : RamState) : Effect :=
  { rip := 0x1033e3
    writes := [⟨(Operand.reg 9 : Operand 64), (Operand.mem (stackPtr s + 8) : Operand 64).read s - 1⟩,
      ⟨(Operand.reg 15 : Operand 64), (Operand.mem (stackPtr s + 32) : Operand 64).read s⟩,
      ⟨(Operand.reg 3 : Operand 64), (Operand.mem (stackPtr s + 24) : Operand 64).read s⟩]
    flags := some ⟨none, none, none,
      some (((Operand.mem (stackPtr s + 32) : Operand 64).read s) == 0), none, none⟩ }

theorem end_setup [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary EndSetupPre (codeRange 0x1033ce endSetupBytes)
      (Effect.post endSetupEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x1033ce 0x4c (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case pre => intro s h; exact ⟨h.rip, h.cursor⟩
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x33d3 (by decide))
  advance_then (dec_r64_effect_step 0x1033d3 0x49 0xc9 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1033ce endSetupBytes 5 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x33d6 (by decide))⟩
  advance_then (mov_r64_m64_effect_step 0x1033d6 0x4c (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1033ce endSetupBytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x33db (by decide))⟩
    x86_norm
    exact hP.remaining
  advance_then (test_r64_r64_effect_step 0x1033db 0x4d 0xff (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1033ce endSetupBytes 13 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x33de (by decide))⟩
  advance_then (mov_r64_m64_effect_step 0x1033de 0x48 (by simp [RexWPrefix]) 3
    (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1033ce endSetupBytes 16 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x33e3 (by decide))⟩
    x86_norm
    exact hP.table
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [endSetupEffect]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [endSetupEffect]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [endSetupEffect]
    simp only [BitVec.and_self]
  · x86_norm [endSetupEffect]
    all_goals (repeat first | constructor | rfl)
end P256.Proofs.Projective.Multiply.Machine.Loop.Round
