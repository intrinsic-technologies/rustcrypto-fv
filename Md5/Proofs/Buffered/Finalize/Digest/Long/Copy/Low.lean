import Md5.Proofs.Buffered.Finalize.Digest.Long.Copy.Tactics

namespace Md5.Proofs.Buffered.Finalize.Digest.Long.Copy

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

set_option maxRecDepth 1024 in
set_option maxHeartbeats 600000 in
theorem low_execution [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (PartPre .low)
      (codeRange (Part.entry .low) (Part.bytes .low))
      (partEffect .low) := by
  change AdvancesBlock boundary (PartPre .low)
    (codeRange 0x10015e [
      0x48, 0x8b, 0x44, 0x24, 0x30, 0x48, 0x89, 0x84, 0x24, 0x88, 0x0, 0x0, 0x0, 0x48,
      0x8b, 0x44, 0x24, 0x28, 0x48, 0x89, 0x84, 0x24, 0x80, 0x0, 0x0, 0x0, 0x48, 0x8b,
      0x44, 0x24, 0x18, 0x48, 0x8b, 0x4c, 0x24, 0x20, 0x48, 0x89, 0x4c, 0x24, 0x78, 0x48,
      0x89, 0x44, 0x24, 0x70]) _
  md5_run_begin (mov_r64_m64_effect_step 0x10015e 0x48 (by unfold RexWPrefix; decide)
    0 (.sib 4 none 0 (.d8 48)) (by decide) (by decide) (by decide))
  case pre =>
    intro s h
    exact ⟨h.rip, (h.toStorage.stackWritable 48 8 (by decide)).readable⟩
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x163 (by decide +kernel)
  digest_copy_store 0x100163, 0x10015e, 46, 5, 0, 136,
    (.sib 4 none 0 (.d32 136)), 8
  digest_copy_load 0x10016b, 0x10015e, 13, 0, 40
  digest_copy_store 0x100170, 0x10015e, 46, 18, 0, 128,
    (.sib 4 none 0 (.d32 128)), 8
  digest_copy_load 0x100178, 0x10015e, 26, 0, 24
  digest_copy_load 0x10017d, 0x10015e, 31, 1, 32
  digest_copy_store 0x100182, 0x10015e, 46, 36, 1, 120,
    (.sib 4 none 0 (.d8 120)), 5
  digest_copy_store 0x100187, 0x10015e, 46, 41, 0, 112,
    (.sib 4 none 0 (.d8 112)), 5
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
