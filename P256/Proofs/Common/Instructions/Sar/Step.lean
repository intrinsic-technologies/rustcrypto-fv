import X86Proofs.Step.AfterStep
import X86Proofs.Step.LegacyStep
import P256.Proofs.Common.Instructions.Sar.Decode
import P256.Proofs.Common.Instructions.Sar.Form

namespace P256.Proofs.Common.Instructions

open X86 X86.Machine X86.UserProcess X86Proofs X86.Helpers

theorem sar_r64_imm8_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex modrm imm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7)
    (hcode : BytesAt s s.RIP [rex, 0xC1, modrm, imm]) (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    let dst : Operand 64 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    let c := shiftCount 64 imm.toBitVec
    X86.Machine.step s = some (.next (afterStep s 4 fun t =>
      writeOutputs t dst (sarSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (sarOracleAF t.oracle c) c (dst.read t))
        (sarOracleBits c) (BitVec.add s.RIP 4#64))) := by
  have hdecode := decodeLegacy0_run_of_rex_C1_sar s h rex modrm imm hmod hreg hcode hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have himm : (Mem_Fetch (BitVec.add s.RIP 3#64) 8).run (afterFetches (beforeFetch s) 4) =
      (.ok imm.toBitVec, afterFetches (beforeFetch s) 5) :=
    memFetch_run_of_bytesAt (beforeFetch s) 4 h.fetchReady hcode hlow 3 (by simp) (by decide)
  rw [sar_r_imm8_form _ _ _ _ _ _ (hmode 4) himm (hmode 5)
    (hrex.operand_size s.DS) rfl,
    show BitVec.add (BitVec.add s.RIP 3#64) 1#64 = BitVec.add s.RIP 4#64 from
      BitVec.add_assoc s.RIP 3#64 1#64] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h rex 0xC1 [modrm, imm] hrex.rexPrefix
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode ((hmode 5).of_cs_lma_eq rfl rfl)

theorem sar_r64_imm8_ready [Bindings] {s : RamState} (h : ReadyToStep s)
    (rex modrm imm : UInt8) :
    let dst : Operand 64 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    let c := shiftCount 64 imm.toBitVec
    ReadyToStep (afterStep s 4 fun t =>
      writeOutputs t dst (sarSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (sarOracleAF t.oracle c) c (dst.read t))
        (sarOracleBits c) (BitVec.add s.RIP 4#64)) :=
  ReadyToStep.afterStep_writeOutputs h 4 _ _ _ _

end P256.Proofs.Common.Instructions
