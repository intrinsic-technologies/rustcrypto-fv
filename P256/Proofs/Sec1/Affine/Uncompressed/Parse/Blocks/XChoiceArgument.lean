import P256.Proofs.SignatureFromDer.Parser.ReadSlice.Execution
import P256.Proofs.Common.Instructions.MovzxByte
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Parse.Blocks

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SignatureFromDer.Parser.ReadSlice
open P256.Proofs.Common.Instructions.MovzxByte

def xChoiceArgumentBytes : List UInt8 :=
  [0x40, 0xf, 0xb6, 0xfd]

def xChoiceArgumentEffect (s : RamState) : Effect :=
  { rip := 0x110905
    writes := [⟨(.reg 7 : Operand 64), ((Operand.reg 5 : Operand 64).read s).setWidth 8 |>.setWidth 64⟩] }

set_option maxHeartbeats 800000 in
theorem x_choice_argument_correct [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s => s.RIP = 0x110901)
      (codeRange 0x110901 xChoiceArgumentBytes) xChoiceArgumentEffect := by
  have width (x : BitVec 8) : ((x.setWidth 64).setWidth 32).setWidth 64 = x.setWidth 64 := by
    rw [BitVec.setWidth_setWidth_of_le x (show 32 ≤ 64 by decide),
      BitVec.setWidth_setWidth (by decide)]
  unfold xChoiceArgumentBytes
  slice_run_begin (show StepEffect _ _ (movzxR32R8Effect 0x110901 4 7 5) from
    movzx_r32_r8_rex_effect_step 0x110901 0x40 0xfd (by simp [RexNoWPrefix]) rfl)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10905 (by decide))
  apply P256.Proofs.Common.Field.AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · x86_norm [xChoiceArgumentEffect, width]
    all_goals repeat first | constructor | rfl
  · x86_norm [xChoiceArgumentEffect, width]
    all_goals repeat first | constructor | rfl
  · intro f; cases f <;> x86_norm [xChoiceArgumentEffect, width]
    all_goals repeat first | constructor | rfl
  · x86_norm [xChoiceArgumentEffect, width]
    all_goals repeat first | constructor | rfl

end P256.Proofs.Sec1.Affine.Uncompressed.Parse.Blocks
