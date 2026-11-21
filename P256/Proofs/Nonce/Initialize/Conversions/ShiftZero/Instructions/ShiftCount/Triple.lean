import P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.Instructions.ShiftCount.Step
import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode
import X86Proofs.Core.Gpr
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Program.Compose

namespace P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.Instructions.ShiftCount

open X86 X86.Machine X86.UserProcess X86Proofs

def shrR64CLEffect (p : BitVec 64) (dst : BitVec 5) (s : RamState) : Effect :=
  shrR64Effect p 3 dst (clCount s) s

theorem shr_r64_cl_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 5) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xD3, modrm])
      (shrR64CLEffect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, shr_r64_cl_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), shr_r64_cl_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, shrSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply shrFlags_allows

end P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.Instructions.ShiftCount
