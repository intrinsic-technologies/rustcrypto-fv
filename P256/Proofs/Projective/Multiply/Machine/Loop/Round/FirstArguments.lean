import P256.Proofs.Projective.Multiply.Machine.Loop.Initial.Setup
import X86Proofs.Instructions.Dec.Generated.R.Triple
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Projective.Multiply.Machine.Loop.Round

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs

structure FirstArgumentsPre (s : RamState) : Prop where
  rip : s.RIP = 0x103340
  writable : P256.Proofs.Common.Instructions.CrossPageStore.Writable s (stackPtr s + 8) 8
  apart : RangeApart (stackPtr s + 8) 8 0x103340 11
def firstArgumentsBytes : List UInt8 :=
  [76, 137, 76, 36, 8, 76, 137, 239, 72, 137, 197]

def firstArgumentsEffect (s : RamState) : Effect :=
  { rip := 0x10334b
    writes := [⟨(Operand.mem (stackPtr s + 8) : Operand 64), s.regValue .r9⟩,
      ⟨(Operand.reg 7 : Operand 64), s.regValue .r13⟩,
      ⟨(Operand.reg 5 : Operand 64), s.regValue .rax⟩] }

theorem firstArguments_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary FirstArgumentsPre (codeRange 0x103340 firstArgumentsBytes)
      (Effect.post firstArgumentsEffect) := by
  advance_begin (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x103340 0x4c (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.writable, fun i hi j hj he => hP.apart i hi j (by change j < 5 at hj; omega) he⟩
  case av =>
    intro s hP
    apply Effect.avoids_codeRange
    x86_norm
    exact hP.apart
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x3345 (by decide))
  advance_then (mov_r64_r64_effect_step 0x103345 0x4c 0xef (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x103340 firstArgumentsBytes 5 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x3348 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x103348 0x48 0xc5 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x103340 firstArgumentsBytes 8 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x334b (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [firstArgumentsEffect, BitVec.shiftLeft_zero, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [firstArgumentsEffect, BitVec.shiftLeft_zero, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [firstArgumentsEffect, BitVec.shiftLeft_zero, BitVec.add_zero]
  · x86_norm [firstArgumentsEffect, BitVec.shiftLeft_zero, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)

end P256.Proofs.Projective.Multiply.Machine.Loop.Round
