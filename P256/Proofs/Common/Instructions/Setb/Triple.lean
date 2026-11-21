import P256.Proofs.Common.Instructions.Setb.Step
import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode
import X86Proofs.Core.Gpr
import X86Proofs.Program.Effect

namespace P256.Proofs.Common.Instructions.Setb

open X86 X86.Machine X86.UserProcess X86Proofs

def setccR8Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (cc : BitVec 4) (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 8 (setccValue cc s) s.GPR[gprIndex dst]⟩] }

theorem setccR8Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (cc : BitVec 4) (s : RamState) :
    (setccR8Effect p len dst cc s).components = [.reg dst, .rip] := rfl

theorem setccR8Effect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (cc : BitVec 4) (s : RamState) (code : CodeMap) :
    (setccR8Effect p len dst cc s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [setccR8Effect_components, Component.Covers]) code

theorem setcc_r8_rex_effect_step [Bindings] (p : BitVec 64) (rex opcode modrm : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hop : SupportedOpcode opcode) (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0x0F, opcode, modrm])
      (setccR8Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (opcode.toBitVec.extractLsb' 0 4)) := by
  rintro s h hcode rfl
  refine ⟨_, setcc_r8_rex_step s h rex opcode modrm hrex hop hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), ReadyToStep.afterStep_writeResult h 4 _ _ _,
    ⟨afterStep_writeResult_rip h 4 _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s 4 _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [writeResult, Operand.write, Operand.read_reg64, Fin.getElem_fin, Vector.getElem_set_self]
  rfl

theorem setcc_r8_effect_step [Bindings] (p : BitVec 64) (opcode modrm : UInt8)
    (hop : SupportedOpcode opcode) (hmod : modrmMod modrm = 3)
    (hlowReg : (gprNumber 0 0 (modrmRm modrm)).toNat < 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x0F, opcode, modrm])
      (setccR8Effect p 3 (gprNumber 0 0 (modrmRm modrm))
        (opcode.toBitVec.extractLsb' 0 4)) := by
  rintro s h hcode rfl
  refine ⟨_, setcc_r8_step s h opcode modrm hop hmod hlowReg hcode.bytesAt
    (hcode.low (by simp) (by simp)), ReadyToStep.afterStep_writeResult h 3 _ _ _,
    ⟨afterStep_writeResult_rip h 3 _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s 3 _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [writeResult, Operand.write, Operand.read_reg64, Fin.getElem_fin, Vector.getElem_set_self]
  rfl

end P256.Proofs.Common.Instructions.Setb
