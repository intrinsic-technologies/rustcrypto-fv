import Hkdf.Proofs.Common.Instructions.Imul.Step
import Hkdf.Proofs.Common.Instructions.Imul.Encode

set_option autoImplicit false

open X86Proofs

namespace Hkdf.Proofs.Common.Instructions

open X86 X86.Machine X86.UserProcess

theorem imul_r64_r64_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0x0F, 0xAF, modrm])
      (imulR64R64Effect p (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, imul_r64_r64_step s h rex modrm hrex hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), ReadyToStep.afterStep_writeOutputs h _ _ _ _ _,
    ⟨afterStep_writeOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, imulSpec64,
      Operand.read_afterFetches, Operand.read_beforeFetch]
  · exact imulFlags64_allows _ _ _

theorem imul_r64_r64_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0x0F, 0xAF, modrm])
      (Effect.post (imulR64R64Effect p (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => imulR64R64Effect_avoids p _ _ s _)
    (imul_r64_r64_effect_step p rex modrm hrex hmod)

theorem imul_r64_r64_effect_step_encoded [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p (encodeImulR64R64 dst src))
      (imulR64R64Effect p (dst.setWidth 5) (src.setWidth 5)) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩ := encodeImulR64R64_spec dst src
  rw [hbytes, ← hdst, ← hsrc]
  exact imul_r64_r64_effect_step p rex modrm hrex hmod

theorem imul_r64_r64_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeImulR64R64 dst src))
      (Effect.post (imulR64R64Effect p (dst.setWidth 5) (src.setWidth 5))) :=
  Triple.of_effect (fun s _ => imulR64R64Effect_avoids p _ _ s _)
    (imul_r64_r64_effect_step_encoded p dst src)

end Hkdf.Proofs.Common.Instructions
