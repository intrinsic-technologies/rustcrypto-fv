import Sha1.Proofs.Buffered.Finalize.Digest.BlockCopy.Tactics

namespace Sha1.Proofs.Buffered.Finalize.Digest.BlockCopy

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Compress.Machine

def longABytes : List UInt8 :=
  [0x48, 0x8b, 0x44, 0x24, 0x50, 0x48, 0x89, 0x84, 0x24, 0xb0, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x44, 0x24, 0x48, 0x48, 0x89, 0x84, 0x24, 0xa8, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x44, 0x24, 0x40, 0x48, 0x89, 0x84, 0x24, 0xa0, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x44, 0x24, 0x38, 0x48, 0x89, 0x84, 0x24, 0x98, 0x0, 0x0, 0x0]

def longAEffect (s : RamState) : Effect :=
  { rip := 0x100170
    writes := [
      ⟨(.reg 0 : Operand 64), (.mem (stackPtr s + 56) : Operand 64).read s⟩,
      ⟨(.mem (stackPtr s + 176) : Operand 64), (.mem (stackPtr s + 80) : Operand 64).read s⟩,
      ⟨(.mem (stackPtr s + 168) : Operand 64), (.mem (stackPtr s + 72) : Operand 64).read s⟩,
      ⟨(.mem (stackPtr s + 160) : Operand 64), (.mem (stackPtr s + 64) : Operand 64).read s⟩,
      ⟨(.mem (stackPtr s + 152) : Operand 64), (.mem (stackPtr s + 56) : Operand 64).read s⟩] }

set_option maxRecDepth 1024 in
set_option maxHeartbeats 1000000 in
theorem longA_execution [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (PartPre 0x10013c) (codeRange 0x10013c longABytes) longAEffect := by
  unfold longABytes
  md5_run_begin (mov_r64_m64_effect_step 0x10013c 0x48 (by unfold RexWPrefix; decide)
    0 (.sib 4 none 0 (.d8 80)) (by decide) (by decide) (by decide))
  case pre =>
    intro s h
    exact ⟨h.rip, (h.toStorage.stackWritable 80 8 (by decide)).readable⟩
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x141 (by decide +kernel)
  digest_copy_store 0x100141, 0x10013c, 52, 5, 0x48, 0, 176,
    (.sib 4 none 0 (.d32 176)), 8
  digest_copy_load 0x100149, 0x10013c, 13, 0, 72
  digest_copy_store 0x10014e, 0x10013c, 52, 18, 0x48, 0, 168,
    (.sib 4 none 0 (.d32 168)), 8
  digest_copy_load 0x100156, 0x10013c, 26, 0, 64
  digest_copy_store 0x10015b, 0x10013c, 52, 31, 0x48, 0, 160,
    (.sib 4 none 0 (.d32 160)), 8
  digest_copy_load 0x100163, 0x10013c, 39, 0, 56
  digest_copy_store 0x100168, 0x10013c, 52, 44, 0x48, 0, 152,
    (.sib 4 none 0 (.d32 152)), 8
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [longAEffect]
  · x86_norm [longAEffect, stackPtr]
    all_goals simp [Operand.read]
  · intro i; cases i <;> x86_norm [longAEffect]
  · x86_norm [longAEffect, stackPtr]
    all_goals simp [Operand.read]

end Sha1.Proofs.Buffered.Finalize.Digest.BlockCopy
