import P256.Proofs.Nonce.Initialize.Conversions.Bsr.Step
import X86Proofs.Program.Effect

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Conversions.Bsr

open X86 X86.Machine X86.UserProcess X86Proofs

def bsrR64R64Effect (p : BitVec 64) (dst src : BitVec 5) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 64).read s
  let b := (Operand.reg src : Operand 64).read s
  { rip := p + 4
    writes := [⟨(Operand.reg dst : Operand 64), (bsrSpec64 a b).1⟩]
    flags := some (.ofStatusFlags (bsrFlags64 b)) }

theorem bsr_r64_r64_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0x0F, 0xBD, modrm])
      (bsrR64R64Effect p (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, bsr_r64_r64_step s h rex modrm hrex hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), ReadyToStep.afterStep_writeOutputs h _ _ _ _ _,
    ⟨afterStep_writeOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, bsrSpec64,
      Operand.read_afterFetches, Operand.read_beforeFetch]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

end P256.Proofs.Nonce.Initialize.Conversions.Bsr
