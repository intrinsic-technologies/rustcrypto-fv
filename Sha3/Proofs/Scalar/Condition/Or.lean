import Sha3.Proofs.Scalar.Condition.Or.Form
import Sha3.Proofs.Scalar.Condition.Or.Decode
import X86Proofs.Program.Effect

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem or_r8_r8_step [Bindings] (s : RamState) (h : ReadyToStep s) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hdst : (gprNumber 0 0 (modrmRm modrm)).toNat < 4)
    (hsrc : (gprNumber 0 0 (modrmReg modrm)).toNat < 4)
    (hcode : BytesAt s s.RIP [0x08, modrm]) (hlow : s.RIP.toNat + 2 ≤ 2 ^ 32) :
    let dst : Operand 8 := .reg (gprNumber 0 0 (modrmRm modrm))
    let src : Operand 8 := .reg (gprNumber 0 0 (modrmReg modrm))
    X86.Machine.step s = some (.next (afterStep s 2 fun t ↦
      writeOutputs t dst (orSpec (oracleBit t.oracle) (dst.read t) (src.read t)) 1
        (BitVec.add s.RIP 2#64))) := by
  have hdecode := decodeLegacy0_run_of_08 s h modrm hmod hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 3) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [or_low_form (afterFetches (beforeFetch s) 3) (BitVec.add s.RIP 2#64)
    (legacyContext s.DS) (modrmReg modrm) (modrmRm modrm) hmode rfl hdst hsrc] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0x08 [modrm]
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode
    (hmode.of_cs_lma_eq rfl rfl)

def orFlags {n : Nat} (r : BitVec n) : StatusFlagsOutcome where
  CF := some false
  PF := some (evenParity (r.extractLsb' 0 8))
  AF := none
  ZF := some (r == 0)
  SF := some r.msb
  OF := some false

def orR8R8Effect (p : BitVec 64) (dst src : BitVec 5) (s : RamState) : Effect :=
  let r := (Operand.reg dst : Operand 8).read s ||| (Operand.reg src : Operand 8).read s
  { rip := p + 2
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 8 r ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (orFlags r) }

theorem orR8R8Effect_components (p : BitVec 64) (dst src : BitVec 5) (s : RamState) :
    (orR8R8Effect p dst src s).components = [.reg dst, .flags, .rip] := rfl

theorem or_r8_r8_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hdst : (gprNumber 0 0 (modrmRm modrm)).toNat < 4)
    (hsrc : (gprNumber 0 0 (modrmReg modrm)).toNat < 4) :
    StepEffect (fun s ↦ s.RIP = p) (codeRange p [0x08, modrm])
      (orR8R8Effect p (gprNumber 0 0 (modrmRm modrm)) (gprNumber 0 0 (modrmReg modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, or_r8_r8_step s h modrm hmod hdst hsrc hcode.bytesAt
    (hcode.low (by simp) (by simp)), ReadyToStep.afterStep_writeOutputs h 2 _ _ 1 _,
    ⟨afterStep_writeOutputs_rip h 2 _ _ 1 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ 1 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self8, orSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem or_cl_al_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = p) (codeRange p [0x08, 0xC1])
      (orR8R8Effect p 1 0) :=
  or_r8_r8_effect_step p 0xC1 (by decide) (by decide) (by decide)

end X86Proofs
