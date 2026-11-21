import P256.Proofs.Common.Instructions.AddByte.Step
import X86Proofs.Program.Effect

set_option autoImplicit false

namespace P256.Proofs.Common.Instructions.AddByte

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

def addR8Imm8Effect (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 8).read s
  { rip := p + 4
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 8 (a + imm) ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (addSpec a imm).2) }

theorem add_r8_imm8_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (imm : BitVec 8) (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 0) :
    StepEffect (fun s => s.RIP = p) (codeRange p (rex :: 0x80 :: modrm :: immBytes 8 imm))
      (addR8Imm8Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm) := by
  rintro s h hcode rfl
  refine ⟨_, add_r8_imm8_step s h rex modrm imm hrex hmod hreg hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), add_r8_imm8_ready h rex modrm imm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp [writeOutputs, Operand.read, Operand.write, addSpec, setFlags,
      afterFetches, beforeFetch, resetStepFields]
  · simpa only [Operand.read_afterFetches, Operand.read_beforeFetch, BitVec.signExtend_eq] using
      StatusFlagsOutcome.allows_ofStatusFlags (addSpec
        ((Operand.reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) : Operand 8).read s) imm).2

theorem add_sil_ff_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x40, 0x80, 0xc6, 0xff])
      (addR8Imm8Effect p 6 0xff) := by
  exact add_r8_imm8_effect_step p 0x40 0xc6 0xff (by simp [RexPrefix]) rfl rfl

theorem add_ff_carry (x : BitVec 8) :
    (addSpec x 0xff).2.CF = decide (x ≠ 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [addSpec, decide_eq_true_eq]
  change (x + 255#8).toNat ≠ x.toNat + 255 ↔ x ≠ 0
  rw [BitVec.toNat_add]
  change (x.toNat + 255) % 256 ≠ x.toNat + 255 ↔ x ≠ 0
  have hx := x.isLt
  have hz : x = 0 ↔ x.toNat = 0 := by rw [← BitVec.toNat_inj]; rfl
  simp only [ne_eq, hz]
  omega

end P256.Proofs.Common.Instructions.AddByte
