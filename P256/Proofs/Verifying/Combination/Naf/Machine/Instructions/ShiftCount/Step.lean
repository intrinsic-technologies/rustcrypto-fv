import X86Proofs.Step.AfterStep
import X86Proofs.Step.LegacyStep
import P256.Proofs.Verifying.Combination.Naf.Machine.Instructions.ShiftCount.Decode
import P256.Proofs.Verifying.Combination.Naf.Machine.Instructions.ShiftCount.Form

open P256.Proofs.Common.Instructions.ShiftLeft (shlOracleAF shlOracleBits shlSpec)

namespace P256.Proofs.Verifying.Combination.Naf.Machine.Instructions.ShiftCount

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem shr_r64_cl_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 5)
    (hcode : BytesAt s s.RIP [rex, 0xD3, modrm]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    let dst : Operand 64 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    let c := clCount s
    X86.Machine.step s = some (.next (afterStep s 3 fun t =>
      writeOutputs t dst (shrSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (shrOracleAF t.oracle c) c (dst.read t))
        (shrOracleBits c) (BitVec.add s.RIP 3#64))) := by
  have hdecode := decodeLegacy0_run_of_rex_D3_shr s h rex modrm hmod hreg hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 4) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [shr_r64_cl_form _ _ _ _ hmode (hrex.operand_size s.DS) rfl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h rex 0xD3 [modrm] hrex.rexPrefix
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem shr_r64_cl_ready [Bindings] {s : RamState} (h : ReadyToStep s) (rex modrm : UInt8) :
    let dst : Operand 64 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    let c := clCount s
    ReadyToStep (afterStep s 3 fun t =>
      writeOutputs t dst (shrSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (shrOracleAF t.oracle c) c (dst.read t))
        (shrOracleBits c) (BitVec.add s.RIP 3#64)) :=
  ReadyToStep.afterStep_writeOutputs h 3 _ _ _ _

theorem shl_r64_cl_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4)
    (hcode : BytesAt s s.RIP [rex, 0xD3, modrm]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    let dst : Operand 64 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    let c := clCount s
    X86.Machine.step s = some (.next (afterStep s 3 fun t =>
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
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem shl_r64_cl_ready [Bindings] {s : RamState} (h : ReadyToStep s) (rex modrm : UInt8) :
    let dst : Operand 64 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    let c := clCount s
    ReadyToStep (afterStep s 3 fun t =>
      writeOutputs t dst (shlSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (shlOracleAF t.oracle c) c (dst.read t))
        (shlOracleBits c) (BitVec.add s.RIP 3#64)) :=
  ReadyToStep.afterStep_writeOutputs h 3 _ _ _ _

end P256.Proofs.Verifying.Combination.Naf.Machine.Instructions.ShiftCount
