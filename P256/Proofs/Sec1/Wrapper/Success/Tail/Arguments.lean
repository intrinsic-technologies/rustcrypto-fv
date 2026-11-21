import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.Wrapper.Success.Tail

open P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

def argumentsBytes : List UInt8 := [72,141,123,8,72,137,230,76,137,250]

def argumentsEffect (s : RamState) : Effect :=
  { rip := 0x1018cd
    writes := [⟨(.reg 7 : Operand 64), (Operand.reg 3 : Operand 64).read s + 8⟩,
      ⟨(.reg 6 : Operand 64), (Operand.reg 4 : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), (Operand.reg 15 : Operand 64).read s⟩] }

theorem prepare_arguments [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1018c3)
      (codeRange 0x1018c3 argumentsBytes) (Effect.post argumentsEffect) := by
  advance_begin (lea_r64_effect_step 0x1018c3 0x48 (by simp [RexWPrefix]) 7
    (.base 3 (.d8 8)) (by decide) rfl rfl)
  case next =>
    exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0x18c7 (by decide))
  advance_then (mov_r64_r64_effect_step 0x1018c7 0x48 0xe6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1018c3 argumentsBytes 4 3
  case mid =>
    intro s t hp he ho
    refine ⟨he.rip, ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x18ca (by decide))
  advance_then (mov_r64_r64_effect_step 0x1018ca 0x4c 0xfa (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1018c3 argumentsBytes 7 3
  case mid =>
    intro s t hp he ho
    refine ⟨he.rip, ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x18cd (by decide))
  advance_finish [argumentsEffect]

end P256.Proofs.Sec1.Wrapper.Success.Tail
