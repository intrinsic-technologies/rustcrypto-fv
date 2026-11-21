import P256.Proofs.Sec1.Affine.State
import P256.Proofs.SignatureFromDer.Parser.ReadSlice.Execution
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Instructions.ByteLogic.XorImmediate
import P256.Proofs.Common.Instructions.ByteLogic.AndReg
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compact.Flags

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SignatureFromDer.Parser.ReadSlice
open P256.Proofs.Common.Encoding.Parser.ResultTag
open P256.Proofs.Common.Instructions.ByteLogic

structure ValuePre (s : RamState) : Prop where
  rip : s.RIP = 0x110283
  readable : MemReadable s (stackPtr s + 80) 1

def valueBytes : List UInt8 :=
  [0x44,0x0f,0xb6,0x74,0x24,0x50,0x41,0x80,0xf6,1,
   0x41,0x20,0xc6,0x41,0x80,0xf6,1]

def flagValue (s : RamState) : BitVec 8 :=
  ((memLoad s.external (stackPtr s + 80) 8 ^^^ 1) &&&
    (s.regValue .rax).setWidth 8) ^^^ 1

def valueEffect (s : RamState) : Effect :=
  { rip := 0x110294
    writes := [⟨(.reg 14 : Operand 64),
      mergeGPR 8 (flagValue s) ((memLoad s.external (stackPtr s + 80) 8).setWidth 64)⟩]
    flags := some (xorFlags (flagValue s)) }

set_option maxHeartbeats 800000 in
theorem value_correct [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary ValuePre (codeRange 0x110283 valueBytes) valueEffect := by
  unfold valueBytes
  slice_run_begin (show StepEffect _ _ (movzxR32M8Effect 0x110283 6 14 (.sib 4 none 0 (.d8 80))) from
    movzx_r32_m8_rex_effect_step 0x110283 0x44 (by simp [RexNoWPrefix])
      6 (.sib 4 none 0 (.d8 80)) (by decide) rfl rfl)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10289 (by decide))
  slice_run_then (show StepEffect _ _ (xorR8Imm8Effect 0x110289 4 14 1) from
    xor_r8_imm8_effect_step 0x110289 0x41 0xf6 1 (by simp [RexPrefix]) rfl rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x110283) 6 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x1028d (by decide))
  slice_run_then (show StepEffect _ _ (andR8R8Effect 0x11028d 14 0) from
    and_r8_r8_rex_effect_step 0x11028d 0x41 0xc6 (by simp [RexPrefix]) rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x110283) 10 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10290 (by decide))
  slice_run_then (show StepEffect _ _ (xorR8Imm8Effect 0x110290 4 14 1) from
    xor_r8_imm8_effect_step 0x110290 0x41 0xf6 1 (by simp [RexPrefix]) rfl rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x110283) 13 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10294 (by decide))
  apply P256.Proofs.Common.Field.AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · x86_norm [valueEffect, flagValue]
  · x86_norm [valueEffect, flagValue]
    simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),
      BitVec.setWidth_eq, mergeGPR_mergeGPR 8 (by decide)]
    rfl
  · intro f; cases f <;> x86_norm [valueEffect, flagValue]
    all_goals simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64), BitVec.setWidth_eq]
    all_goals rfl
  · x86_norm [valueEffect, flagValue]

end P256.Proofs.Sec1.Affine.Compact.Flags
