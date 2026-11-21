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

def b1164f7Bytes : List UInt8 :=
  [72, 137, 239, 76, 137, 238]

def b1164f7Effect (s : RamState) : Effect :=
  { rip := 0x10e78d
    writes := [⟨(Operand.reg 7 : Operand 64), (Operand.reg 5 : Operand 64).read s⟩,
      ⟨(Operand.reg 6 : Operand 64), (Operand.reg 13 : Operand 64).read s⟩] }

theorem b1164f7_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10e787)
      (codeRange 0x10e787 b1164f7Bytes) (Effect.post b1164f7Effect) := by
  advance_begin (mov_r64_r64_effect_step 0x10e787 0x48 0xef (by simp [RexWPrefix]) rfl)
  case next => intro _ _; exact boundary_ne_program hout (inProgram_of_textOffset 0xe78a (by decide))
  advance_then (mov_r64_r64_effect_step 0x10e78a 0x4c 0xee (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10e787 b1164f7Bytes 3 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xe78d (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [b1164f7Effect, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [b1164f7Effect, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [b1164f7Effect, BitVec.add_zero]
  · x86_norm [b1164f7Effect, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)

end P256.Proofs.Projective.Multiply.Machine.Basepoint.Blocks
