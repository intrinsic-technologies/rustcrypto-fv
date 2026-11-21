import P256.Proofs.SignatureFromDer.Parser.ReadSlice.Execution
import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Curve

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SignatureFromDer.Parser.ReadSlice

def compareArgumentsBytes : List UInt8 :=
  [0x48, 0x89, 0xef, 0x4c, 0x89, 0xf6]

def compareArgumentsEffect (s : RamState) : Effect :=
  { rip := 0x110be0
    writes := [⟨(.reg 7 : Operand 64), (Operand.reg 5 : Operand 64).read s⟩,
      ⟨(.reg 6 : Operand 64), (Operand.reg 14 : Operand 64).read s⟩] }

set_option maxHeartbeats 800000 in
theorem compareArguments_correct [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s => s.RIP = 0x110bda)
      (codeRange 0x110bda compareArgumentsBytes) compareArgumentsEffect := by
  unfold compareArgumentsBytes
  slice_run_begin (show StepEffect _ _ (movR64R64Effect 0x110bda 7 5) from
    mov_r64_r64_effect_step 0x110bda 0x48 0xef (by simp [RexWPrefix]) rfl)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10bdd (by decide))
  slice_run_then (show StepEffect _ _ (movR64R64Effect 0x110bdd 6 14) from
    mov_r64_r64_effect_step 0x110bdd 0x4c 0xf6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x110bda) 3 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10be0 (by decide))
  apply P256.Proofs.Common.Field.AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · x86_norm [compareArgumentsEffect] <;> rfl
  · x86_norm [compareArgumentsEffect] <;> rfl
  · intro f; cases f <;> x86_norm [compareArgumentsEffect]
  · x86_norm [compareArgumentsEffect] <;> rfl

end P256.Proofs.Sec1.Affine.Uncompressed.Curve
