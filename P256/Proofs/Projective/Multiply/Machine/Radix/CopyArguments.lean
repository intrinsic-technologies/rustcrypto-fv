import P256.Proofs.Projective.Multiply.Machine.Radix.Code
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Radix

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs Program
open P256.Proofs.Common.Field

def copyArgumentsBytes : List UInt8 :=
  [0x48,0x8d,0x74,0x24,8,0xba,65,0,0,0,0x48,0x89,0xdf]

def copyArgumentsEffect (s : RamState) : Effect :=
  { rip := 0x10ba79
    writes := [⟨(.reg 6 : Operand 64),stackPtr s+8⟩,
      ⟨(.reg 2 : Operand 64),65⟩,⟨(.reg 7 : Operand 64),s.regValue .rbx⟩] }

theorem copy_arguments [Bindings] (boundary : ReturnBoundary) (outside : ¬InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP=0x10ba6c) (codeRange 0x10ba6c copyArgumentsBytes)
      (Effect.post copyArgumentsEffect) := by
  advance_begin (lea_r64_effect_step 0x10ba6c 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xba71 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10ba71 0xba (by decide) 65)
  case sub => exact codeRange_slice_subset 0x10ba6c copyArgumentsBytes 5 5
  case mid =>
    intro s t hp he ho
    refine ⟨he.rip,?_,?_⟩
    · x86_avoid
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xba76 (by decide))
  advance_then (mov_r64_r64_effect_step 0x10ba76 0x48 0xdf (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10ba6c copyArgumentsBytes 10 3
  case mid =>
    intro s t hp he ho
    refine ⟨he.rip,?_,?_⟩
    · x86_avoid
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xba79 (by decide))
  advance_finish [copyArgumentsEffect]

end P256.Proofs.Projective.Multiply.Machine.Radix
