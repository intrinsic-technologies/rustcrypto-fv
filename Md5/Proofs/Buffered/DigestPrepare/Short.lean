import Md5.Proofs.Buffered.DigestPrepare.Geometry
import Md5.Proofs.Buffered.DigestPrepare.Branch
import Md5.Proofs.Buffered.Update.Calls
import Md5.Proofs.Buffered.Update.Rodata
import Md5.Proofs.Buffered.Finalize.Store8
import Md5.Proofs.Block.Rounds.Register.Lea
import Md5.Proofs.Block.Execution
import Md5.Proofs.MemoryRoutines.Register.Compose

namespace Md5.Proofs.Buffered.DigestPrepare

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

def shortCopyBytes : List UInt8 :=
  [0x48, 0x8d, 0xbc, 0x24, 0xb0, 0, 0, 0, 0x4c, 0x89, 0xfa]

def shortCopyEffect (s : RamState) : Effect :=
  { rip := 0x100078
    writes := [⟨(.reg 7 : Operand 64), stackPtr s + 176⟩,
      ⟨(.reg 2 : Operand 64), (.reg 15 : Operand 64).read s⟩] }

theorem short_copy_prepare [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x10006d)
      (codeRange 0x10006d shortCopyBytes) shortCopyEffect := by
  unfold shortCopyBytes
  md5_run_begin lea_r64_effect_step 0x10006d 0x48 (by unfold RexWPrefix; decide)
    7 (.sib 4 none 0 (.d32 176)) (by decide) (by decide) (by decide)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x75 (by decide +kernel)
  md5_run_then mov_r64_r64_effect_step 0x100075 0x4c 0xfa
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x10006d) 8 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x78 (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ he
  apply he.weaken
  · x86_norm [shortCopyEffect]
  · x86_norm [shortCopyEffect, stackPtr]
    simp [Operand.read, gprNumber, rexR, modrmReg]
  · intro i; cases i <;> x86_norm [shortCopyEffect]
  · x86_norm [shortCopyEffect]

end Md5.Proofs.Buffered.DigestPrepare
