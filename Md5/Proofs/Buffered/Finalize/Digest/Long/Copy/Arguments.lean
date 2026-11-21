import Md5.Proofs.Buffered.Finalize.Digest.Long.Copy.Tactics

namespace Md5.Proofs.Buffered.Finalize.Digest.Long.Copy

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

set_option maxRecDepth 1024 in
set_option maxHeartbeats 600000 in
theorem arguments_execution [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (PartPre .arguments)
      (codeRange (Part.entry .arguments) (Part.bytes .arguments))
      (partEffect .arguments) := by
  change AdvancesBlock boundary (PartPre .arguments)
    (codeRange 0x10018c [
      0x48, 0x8d, 0x7c, 0x24, 0x8, 0x48, 0x8d, 0x74, 0x24, 0x70, 0xba, 0x1, 0x0, 0x0,
      0x0]) _
  md5_run_begin (lea_r64_effect_step 0x10018c 0x48 (by unfold RexWPrefix; decide)
    7 (.sib 4 none 0 (.d8 8)) (by decide) (by decide) (by decide))
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x191 (by decide +kernel)
  md5_run_then (lea_r64_effect_step 0x100191 0x48 (by unfold RexWPrefix; decide)
    6 (.sib 4 none 0 (.d8 112)) (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x10018c) 5 (by decide +kernel)
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x196 (by decide +kernel)
  md5_run_then (mov_r32_imm32_effect_step 0x100196 0xba (by decide) 1)
  case sub => exact codeRange_mem_of_drop (p := 0x10018c) 10 (by decide +kernel)
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x19b (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [partEffect, Part.entry, Part.offset, Part.length]
  · x86_norm [partEffect, wordWrite, stackPtr]
    all_goals simp [Operand.read]
  · intro i; cases i <;> x86_norm [partEffect]
  · x86_norm [partEffect, wordWrite, stackPtr]
    all_goals simp [Operand.read]

end Md5.Proofs.Buffered.Finalize.Digest.Long.Copy
