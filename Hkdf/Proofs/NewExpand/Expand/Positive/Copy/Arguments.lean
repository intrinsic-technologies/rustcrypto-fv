import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Mov.Triple

namespace Hkdf.Proofs.NewExpand.Expand

open Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Machine Hkdf.Proofs.Common.Field

def copyArgumentsBytes : List UInt8 := [0x4c,0x89,0xf7,0x4c,0x89,0xee,0x48,0x89,0xda]

def copyArgumentsEffect (s : RamState) : Effect where
  rip := 0x10f545
  writes := [⟨(.reg 7 : Operand 64), (.reg 14 : Operand 64).read s⟩,
    ⟨(.reg 6 : Operand 64), (.reg 13 : Operand 64).read s⟩, ⟨(.reg 2 : Operand 64), (.reg 3 : Operand 64).read s⟩]

theorem copyArguments [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10f53c)
      (codeRange 0x10f53c copyArgumentsBytes) (Effect.post copyArgumentsEffect) := by
  advance_begin mov_r64_r64_effect_step 0x10f53c 0x4c 0xf7 (by simp [RexWPrefix]) rfl
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xf53f (by decide))
  advance_then mov_r64_r64_effect_step 0x10f53f 0x4c 0xee (by simp [RexWPrefix]) rfl
  case sub => exact codeRange_slice_subset 0x10f53c copyArgumentsBytes 3 3
  case mid =>
    intro s t _ eff _
    exact ⟨eff.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0xf542 (by decide))⟩
  advance_then mov_r64_r64_effect_step 0x10f542 0x48 0xda (by simp [RexWPrefix]) rfl
  case sub => exact codeRange_slice_subset 0x10f53c copyArgumentsBytes 6 3
  case mid =>
    intro s t _ eff _
    exact ⟨eff.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0xf545 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t _ eff
  exact eff

end Hkdf.Proofs.NewExpand.Expand
