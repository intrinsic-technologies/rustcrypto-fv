import P256.Proofs.Projective.Multiply.Machine.Loop.Initial.Setup
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Projective.Multiply.Machine.Loop.Initial

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure ArgumentsPre (s : RamState) : Prop where
  rip : s.RIP = 0x1032c8
  readable : MemReadable s (s.regValue .r9 + s.regValue .r13 + 64) 1

def argumentsBytes : List UInt8 :=
  [0x43,0x0f,0xb6,0x54,0x29,0x40,0x4c,0x8d,0xa4,0x24,0x88,0,0,0,
    0x4c,0x89,0xe7,0x4c,0x89,0xfe,0x4c,0x89,0xcd]

def argumentsEffect (s : RamState) : Effect :=
  { rip := 0x1032df
    writes := [⟨(Operand.reg 2 : Operand 64),
        ((Operand.mem (s.regValue .r9 + s.regValue .r13 + 64) : Operand 8).read s).setWidth 64⟩,
      ⟨(Operand.reg 12 : Operand 64), stackPtr s + 136⟩,
      ⟨(Operand.reg 7 : Operand 64), stackPtr s + 136⟩,
      ⟨(Operand.reg 6 : Operand 64), s.regValue .r15⟩,
      ⟨(Operand.reg 5 : Operand 64), s.regValue .r9⟩] }

theorem arguments_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary ArgumentsPre (codeRange 0x1032c8 argumentsBytes)
      (Effect.post argumentsEffect) := by
  advance_begin (movzx_r_m8_rex_effect_step 0x1032c8 0x43 (by simp [RexPrefix]) 32
    (Or.inr rfl) (by intro seg; rfl) 2 (.sib 9 (some 13) 0 (.d8 64))
    (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    refine ⟨hP.rip, ?_⟩
    change MemReadable s (s.regValue .r9 + (s.regValue .r13 <<< 0) + 64) 1
    simpa using hP.readable
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x32ce (by decide))
  advance_then (lea_r64_effect_step 0x1032ce 0x4c (by simp [RexWPrefix]) 4
    (.sib 4 none 0 (.d32 136)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1032c8 argumentsBytes 6 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x32d6 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x1032d6 0x4c 0xe7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1032c8 argumentsBytes 14 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x32d9 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x1032d9 0x4c 0xfe (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1032c8 argumentsBytes 17 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x32dc (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x1032dc 0x4c 0xcd (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1032c8 argumentsBytes 20 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x32df (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [argumentsEffect]
  · x86_norm [argumentsEffect, BitVec.shiftLeft_zero, BitVec.add_assoc]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [argumentsEffect]
  · x86_norm [argumentsEffect]
    all_goals (repeat first | constructor | rfl)

end P256.Proofs.Projective.Multiply.Machine.Loop.Initial
