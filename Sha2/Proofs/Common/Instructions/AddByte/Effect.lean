import Sha2.Proofs.Common.Instructions.AddByte.Step
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Not.Generated.R.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Movs.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Common.Instructions.AddByte

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

def addR8R8Effect (p : BitVec 64) (dst src : BitVec 5) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 8).read s
  let b := (Operand.reg src : Operand 8).read s
  { rip := p + 3
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 8 (a + b) ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (addSpec a b).2) }

theorem add_r8_r8_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0x00, modrm])
      (addR8R8Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, add_r8_r8_step s h rex modrm hrex hmod hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), ReadyToStep.afterStep_writeOutputs h 3 _ _ 0 _,
    ⟨afterStep_writeOutputs_rip h 3 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp [writeOutputs, Operand.read, Operand.write, addSpec, setFlags,
      afterFetches, beforeFetch, resetStepFields]
  · simpa only [Operand.read_afterFetches, Operand.read_beforeFetch, BitVec.signExtend_eq] using
      StatusFlagsOutcome.allows_ofStatusFlags (addSpec
        ((Operand.reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) : Operand 8).read s)
        ((Operand.reg (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) : Operand 8).read s)).2

theorem add_bl_r12b_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x44, 0x00, 0xe3])
      (addR8R8Effect p 3 12) :=
  add_r8_r8_effect_step p 0x44 0xe3 (by simp [RexPrefix]) rfl

attribute [x86_compose] addR8R8Effect

end Sha2.Proofs.Common.Instructions.AddByte
