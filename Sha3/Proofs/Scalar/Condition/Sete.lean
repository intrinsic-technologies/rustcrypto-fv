import Sha3.Proofs.Scalar.Condition.Sete.Form
import Sha3.Proofs.Scalar.Condition.Sete.Decode
import X86Proofs.Program.Effect

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem sete_r8_step [Bindings] (s : RamState) (h : ReadyToStep s) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hdst : (gprNumber 0 0 (modrmRm modrm)).toNat < 4)
    (hcode : BytesAt s s.RIP [0x0F, 0x94, modrm]) (hlow : s.RIP.toNat + 3 ≤ 2 ^ 32) :
    X86.Machine.step s = some (.next (afterStep s 3 fun t ↦
      writeResult t (.reg (gprNumber 0 0 (modrmRm modrm)))
        (setccSpec 4 (StatusFlags.ofRFLAGS s.RFLAGS)) (BitVec.add s.RIP 3#64))) := by
  have hdecode := decodeLegacy1_run_of_94_register s h modrm hmod hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 4) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [sete_low_form (afterFetches (beforeFetch s) 4) (BitVec.add s.RIP 3#64)
    (legacyContext s.DS) (modrmRm modrm) hmode rfl hdst] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy1 s _ h 0x94 [modrm] ⟨by decide, by decide⟩ hcode hlow hdecode
    (hmode.of_cs_lma_eq rfl rfl)

def seteR8Effect (p : BitVec 64) (dst : BitVec 5) (s : RamState) : Effect :=
  { rip := p + 3
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 8 (if (StatusFlags.ofRFLAGS s.RFLAGS).ZF then 1 else 0)
        ((Operand.reg dst : Operand 64).read s)⟩] }

theorem seteR8Effect_components (p : BitVec 64) (dst : BitVec 5) (s : RamState) :
    (seteR8Effect p dst s).components = [.reg dst, .rip] := rfl

theorem sete_r8_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hdst : (gprNumber 0 0 (modrmRm modrm)).toNat < 4) :
    StepEffect (fun s ↦ s.RIP = p) (codeRange p [0x0F, 0x94, modrm])
      (seteR8Effect p (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, sete_r8_step s h modrm hmod hdst hcode.bytesAt
    (hcode.low (by simp) (by simp)), ReadyToStep.afterStep_writeResult h 3 _ _ _,
    ⟨afterStep_writeResult_rip h 3 _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s 3 _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self8, Operand.read_afterFetches,
    Operand.read_beforeFetch]
  rfl

theorem sete_al_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = p) (codeRange p [0x0F, 0x94, 0xC0])
      (seteR8Effect p 0) :=
  sete_r8_effect_step p 0xC0 (by decide) (by decide)

theorem sete_cl_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = p) (codeRange p [0x0F, 0x94, 0xC1])
      (seteR8Effect p 1) :=
  sete_r8_effect_step p 0xC1 (by decide) (by decide)

end X86Proofs
