import Sha3.Proofs.Scalar.Shift.Decode
import Sha3.Proofs.Scalar.Shift.Form
import X86Proofs.Step.AfterStep
import X86Proofs.Step.LegacyStep

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem shl_r64_cl_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4)
    (hcode : BytesAt s s.RIP [rex, 0xD3, modrm]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    let dst : Operand 64 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    let c := shiftCount 64 ((Operand.reg 1 : Operand 8).read s)
    X86.Machine.step s = some (.next (afterStep s 3 fun t ↦
      writeOutputs t dst (shlSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (shlOracleAF t.oracle c) c (dst.read t))
        (shlOracleBits c) (BitVec.add s.RIP 3#64))) := by
  have hdecode := decodeLegacy0_run_of_rex_D3_shl s h rex modrm hmod hreg hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 4) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [shl_r64_cl_form _ _ _ _ hmode (hrex.operand_size s.DS) rfl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h rex 0xD3 [modrm] hrex.rexPrefix
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode
    (hmode.of_cs_lma_eq rfl rfl)

theorem shl_r64_cl_ready [Bindings] {s : RamState} (h : ReadyToStep s) (rex modrm : UInt8) :
    let dst : Operand 64 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    let c := shiftCount 64 ((Operand.reg 1 : Operand 8).read s)
    ReadyToStep (afterStep s 3 fun t ↦
      writeOutputs t dst (shlSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (shlOracleAF t.oracle c) c (dst.read t))
        (shlOracleBits c) (BitVec.add s.RIP 3#64)) :=
  ReadyToStep.afterStep_writeOutputs h 3 _ _ _ _

def shlR64ClEffect (p : BitVec 64) (dst : BitVec 5) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 64).read s
  let c := shiftCount 64 ((Operand.reg 1 : Operand 8).read s)
  { rip := p + 3
    writes := [⟨(Operand.reg dst : Operand 64), a <<< c⟩]
    flags := some (shlFlags (StatusFlags.ofRFLAGS s.RFLAGS) c a) }

theorem shlR64ClEffect_components (p : BitVec 64) (dst : BitVec 5) (s : RamState) :
    (shlR64ClEffect p dst s).components = [.reg dst, .flags, .rip] := rfl

theorem shlR64ClEffect_avoids (p : BitVec 64) (dst : BitVec 5) (s : RamState)
    (code : CodeMap) : (shlR64ClEffect p dst s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [shlR64ClEffect_components, Component.Covers]) code

theorem shl_r64_cl_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 4) :
    StepEffect (fun s ↦ s.RIP = p) (codeRange p [rex, 0xD3, modrm])
      (shlR64ClEffect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, shl_r64_cl_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), shl_r64_cl_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, shlSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply shlFlags_allows

theorem shl_rdx_cl_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = p) (codeRange p [0x48, 0xD3, 0xE2])
      (shlR64ClEffect p 2) :=
  shl_r64_cl_effect_step p 0x48 0xE2 (by unfold RexWPrefix; decide +kernel)
    (by decide +kernel) (by decide +kernel)

end X86Proofs
