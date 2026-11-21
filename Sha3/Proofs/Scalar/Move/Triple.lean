import Sha3.Proofs.Scalar.Move.Step
import X86Proofs.Program.Effect

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def movzxR32R8Effect (p : BitVec 64) (dst src : BitVec 5) (s : RamState) : Effect :=
  { rip := p + 4
    writes := [⟨(Operand.reg dst : Operand 64),
      ((Operand.reg src : Operand 8).read s).setWidth 64⟩]
    flags := none }

def cmovbR64R64Effect (p : BitVec 64) (dst src : BitVec 5) (s : RamState) : Effect :=
  { rip := p + 4
    writes := [⟨(Operand.reg dst : Operand 64),
      if (StatusFlags.ofRFLAGS s.RFLAGS).CF then
        (Operand.reg src : Operand 64).read s else (Operand.reg dst : Operand 64).read s⟩]
    flags := none }

theorem movzxR32R8Effect_components (p : BitVec 64) (dst src : BitVec 5) (s : RamState) :
    (movzxR32R8Effect p dst src s).components = [.reg dst, .rip] := rfl

theorem cmovbR64R64Effect_components (p : BitVec 64) (dst src : BitVec 5) (s : RamState) :
    (cmovbR64R64Effect p dst src s).components = [.reg dst, .rip] := rfl

theorem movzx_r32_r8_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0x0F, 0xB6, modrm])
      (movzxR32R8Effect p (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, movzx_r32_r8_rex_step s h rex modrm hrex hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), ReadyToStep.afterStep_writeResult h 4 _ _ _,
    ⟨afterStep_writeResult_rip h 4 _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s 4 _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self32, movzxSpec, Operand.read_afterFetches,
    Operand.read_beforeFetch]
  exact BitVec.setWidth_setWidth (by decide)

theorem cmovb_r64_r64_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0x0F, 0x42, modrm])
      (cmovbR64R64Effect p (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, cmovb_r64_r64_step s h rex modrm hrex hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), ReadyToStep.afterStep_writeResult h 4 _ _ _,
    ⟨afterStep_writeResult_rip h 4 _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s 4 _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self, Operand.read_afterFetches, Operand.read_beforeFetch]

theorem movzx_eax_r14b_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x41, 0x0F, 0xB6, 0xC6])
      (movzxR32R8Effect p 0 14) :=
  movzx_r32_r8_rex_effect_step p 0x41 0xC6 (by simp [RexNoWPrefix]) (by decide)

theorem movzx_ecx_sil_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x40, 0x0F, 0xB6, 0xCE])
      (movzxR32R8Effect p 1 6) :=
  movzx_r32_r8_rex_effect_step p 0x40 0xCE (by simp [RexNoWPrefix]) (by decide)

theorem cmovb_rcx_r8_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x49, 0x0F, 0x42, 0xC8])
      (cmovbR64R64Effect p 1 8) :=
  cmovb_r64_r64_effect_step p 0x49 0xC8 (by simp [RexWPrefix]) (by decide)

end X86Proofs
