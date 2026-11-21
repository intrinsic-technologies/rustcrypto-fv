import Sha3.Proofs.Scalar.Condition.Cmov.Step
import X86Proofs.Program.Effect

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def cmovaeR64R64Effect (p : BitVec 64) (dst src : BitVec 5) (s : RamState) : Effect :=
  { rip := p + 4
    writes := [⟨(Operand.reg dst : Operand 64),
      if (StatusFlags.ofRFLAGS s.RFLAGS).CF then
        (Operand.reg dst : Operand 64).read s else (Operand.reg src : Operand 64).read s⟩]
    flags := none }

theorem cmovaeR64R64Effect_components (p : BitVec 64) (dst src : BitVec 5) (s : RamState) :
    (cmovaeR64R64Effect p dst src s).components = [.reg dst, .rip] := rfl

theorem cmovae_r64_r64_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0x0F, 0x43, modrm])
      (cmovaeR64R64Effect p (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, cmovae_r64_r64_step s h rex modrm hrex hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), ReadyToStep.afterStep_writeResult h 4 _ _ _,
    ⟨afterStep_writeResult_rip h 4 _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s 4 _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self, Operand.read_afterFetches, Operand.read_beforeFetch]

theorem cmovae_r13_rax_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x4C, 0x0F, 0x43, 0xE8])
      (cmovaeR64R64Effect p 13 0) :=
  cmovae_r64_r64_effect_step p 0x4C 0xE8 (by simp [RexWPrefix]) (by decide)

theorem cmovae_rbx_rax_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x48, 0x0F, 0x43, 0xD8])
      (cmovaeR64R64Effect p 3 0) :=
  cmovae_r64_r64_effect_step p 0x48 0xD8 (by simp [RexWPrefix]) (by decide)

end X86Proofs
