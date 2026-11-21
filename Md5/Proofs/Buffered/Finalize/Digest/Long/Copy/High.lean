import Md5.Proofs.Buffered.Finalize.Digest.Long.Copy.Tactics

namespace Md5.Proofs.Buffered.Finalize.Digest.Long.Copy

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

set_option maxRecDepth 1024 in
set_option maxHeartbeats 600000 in
theorem high_execution [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (PartPre .high)
      (codeRange (Part.entry .high) (Part.bytes .high))
      (partEffect .high) := by
  change AdvancesBlock boundary (PartPre .high)
    (codeRange 0x10012a [
      0x48, 0x8b, 0x44, 0x24, 0x50, 0x48, 0x89, 0x84, 0x24, 0xa8, 0x0, 0x0, 0x0, 0x48,
      0x8b, 0x44, 0x24, 0x48, 0x48, 0x89, 0x84, 0x24, 0xa0, 0x0, 0x0, 0x0, 0x48, 0x8b,
      0x44, 0x24, 0x40, 0x48, 0x89, 0x84, 0x24, 0x98, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x44,
      0x24, 0x38, 0x48, 0x89, 0x84, 0x24, 0x90, 0x0, 0x0, 0x0]) _
  md5_run_begin (mov_r64_m64_effect_step 0x10012a 0x48 (by unfold RexWPrefix; decide)
    0 (.sib 4 none 0 (.d8 80)) (by decide) (by decide) (by decide))
  case pre =>
    intro s h
    exact ⟨h.rip, (h.toStorage.stackWritable 80 8 (by decide)).readable⟩
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x12f (by decide +kernel)
  digest_copy_store 0x10012f, 0x10012a, 52, 5, 0, 168,
    (.sib 4 none 0 (.d32 168)), 8
  digest_copy_load 0x100137, 0x10012a, 13, 0, 72
  digest_copy_store 0x10013c, 0x10012a, 52, 18, 0, 160,
    (.sib 4 none 0 (.d32 160)), 8
  digest_copy_load 0x100144, 0x10012a, 26, 0, 64
  digest_copy_store 0x100149, 0x10012a, 52, 31, 0, 152,
    (.sib 4 none 0 (.d32 152)), 8
  digest_copy_load 0x100151, 0x10012a, 39, 0, 56
  digest_copy_store 0x100156, 0x10012a, 52, 44, 0, 144,
    (.sib 4 none 0 (.d32 144)), 8
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
