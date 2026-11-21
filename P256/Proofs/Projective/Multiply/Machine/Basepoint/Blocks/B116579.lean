import P256.Proofs.Program.Code
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Projective.Multiply.Machine.Basepoint.Blocks

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs

def b116579Bytes : List UInt8 :=
  [76, 137, 247, 76, 137, 238]

def b116579Effect (s : RamState) : Effect :=
  { rip := 0x10e80f
    writes := [⟨(Operand.reg 7 : Operand 64), (Operand.reg 14 : Operand 64).read s⟩,
      ⟨(Operand.reg 6 : Operand 64), (Operand.reg 13 : Operand 64).read s⟩] }

theorem b116579_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10e809)
      (codeRange 0x10e809 b116579Bytes) (Effect.post b116579Effect) := by
  advance_begin (mov_r64_r64_effect_step 0x10e809 0x4c 0xf7 (by simp [RexWPrefix]) rfl)
  case next => intro _ _; exact boundary_ne_program hout (inProgram_of_textOffset 0xe80c (by decide))
  advance_then (mov_r64_r64_effect_step 0x10e80c 0x4c 0xee (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10e809 b116579Bytes 3 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xe80f (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [b116579Effect, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [b116579Effect, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [b116579Effect, BitVec.add_zero]
  · x86_norm [b116579Effect, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)

end P256.Proofs.Projective.Multiply.Machine.Basepoint.Blocks
