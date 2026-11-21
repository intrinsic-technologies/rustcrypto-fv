import Sha1.Proofs.Buffered.Finalize.Digest.BlockCopy.Tactics

namespace Sha1.Proofs.Buffered.Finalize.Digest.BlockCopy

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Compress.Machine

def longBBytes : List UInt8 :=
  [0x48, 0x8b, 0x44, 0x24, 0x30, 0x48, 0x89, 0x84, 0x24, 0x90, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x44, 0x24, 0x28, 0x48, 0x89, 0x84, 0x24, 0x88, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x44, 0x24, 0x18, 0x48, 0x8b, 0x4c, 0x24, 0x20, 0x48, 0x89, 0x8c, 0x24, 0x80, 0x0, 0x0, 0x0, 0x48, 0x89, 0x44, 0x24, 0x78]

def longBEffect (s : RamState) : Effect :=
  { rip := 0x1001a1
    writes := [
      ⟨(.reg 0 : Operand 64), (.mem (stackPtr s + 24) : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), (.mem (stackPtr s + 32) : Operand 64).read s⟩,
      ⟨(.mem (stackPtr s + 144) : Operand 64), (.mem (stackPtr s + 48) : Operand 64).read s⟩,
      ⟨(.mem (stackPtr s + 136) : Operand 64), (.mem (stackPtr s + 40) : Operand 64).read s⟩,
      ⟨(.mem (stackPtr s + 128) : Operand 64), (.mem (stackPtr s + 32) : Operand 64).read s⟩,
      ⟨(.mem (stackPtr s + 120) : Operand 64), (.mem (stackPtr s + 24) : Operand 64).read s⟩] }

set_option maxRecDepth 1024 in
set_option maxHeartbeats 1000000 in
theorem longB_execution [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (PartPre 0x100170) (codeRange 0x100170 longBBytes) longBEffect := by
  unfold longBBytes
  md5_run_begin (mov_r64_m64_effect_step 0x100170 0x48 (by unfold RexWPrefix; decide)
    0 (.sib 4 none 0 (.d8 48)) (by decide) (by decide) (by decide))
  case pre =>
    intro s h
    exact ⟨h.rip, (h.toStorage.stackWritable 48 8 (by decide)).readable⟩
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x175 (by decide +kernel)
  digest_copy_store 0x100175, 0x100170, 49, 5, 0x48, 0, 144,
    (.sib 4 none 0 (.d32 144)), 8
  digest_copy_load 0x10017d, 0x100170, 13, 0, 40
  digest_copy_store 0x100182, 0x100170, 49, 18, 0x48, 0, 136,
    (.sib 4 none 0 (.d32 136)), 8
  digest_copy_load 0x10018a, 0x100170, 26, 0, 24
  digest_copy_load 0x10018f, 0x100170, 31, 1, 32
  digest_copy_store 0x100194, 0x100170, 49, 36, 0x48, 1, 128,
    (.sib 4 none 0 (.d32 128)), 8
  digest_copy_store 0x10019c, 0x100170, 49, 44, 0x48, 0, 120,
    (.sib 4 none 0 (.d8 120)), 5
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [longBEffect]
  · x86_norm [longBEffect, stackPtr]
    all_goals simp [Operand.read]
  · intro i; cases i <;> x86_norm [longBEffect]
  · x86_norm [longBEffect, stackPtr]
    all_goals simp [Operand.read]

end Sha1.Proofs.Buffered.Finalize.Digest.BlockCopy
