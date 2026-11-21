import X86Proofs.Step.AfterStep
import X86Proofs.Step.LegacyStep
import X86Proofs.Instructions.Ror.Generated.R.Decode
import Sha2.Proofs.Common.Instructions.Ror.Form



namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers


theorem ror_r64_imm8_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex modrm imm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1)
    (hcode : BytesAt s s.RIP [rex, 0xC1, modrm, imm]) (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    let dst : Operand 64 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    let c := shiftCount 64 imm.toBitVec
    X86.Machine.step s = some (.next (afterStep s 4 fun t =>
      writeOutputs t dst (rorSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) c (dst.read t))
        (rorOracleBits c) (BitVec.add s.RIP 4#64))) := by
  have hdecode := decodeLegacy0_run_of_rex_C1_ror s h rex modrm imm hmod hreg hcode hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have himm : (Mem_Fetch (BitVec.add s.RIP 3#64) 8).run (afterFetches (beforeFetch s) 4) =
      (.ok imm.toBitVec, afterFetches (beforeFetch s) 5) :=
    memFetch_run_of_bytesAt (beforeFetch s) 4 h.fetchReady hcode hlow 3 (by simp) (by decide)
  rw [ror_r_imm8_form _ _ _ _ _ _ (hmode 4) himm (hmode 5) 64 (by decide)
    (hrex.operand_size s.DS) rfl,
    show BitVec.add (BitVec.add s.RIP 3#64) 1#64 = BitVec.add s.RIP 4#64 from
      BitVec.add_assoc s.RIP 3#64 1#64] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h rex 0xC1 [modrm, imm] hrex.rexPrefix
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode ((hmode 5).of_cs_lma_eq rfl rfl)


theorem ror_r64_imm8_ready [Bindings] {s : RamState} (h : ReadyToStep s)
    (rex modrm imm : UInt8) :
    let dst : Operand 64 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    let c := shiftCount 64 imm.toBitVec
    ReadyToStep (afterStep s 4 fun t =>
      writeOutputs t dst (rorSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) c (dst.read t))
        (rorOracleBits c) (BitVec.add s.RIP 4#64)) :=
  ReadyToStep.afterStep_writeOutputs h 4 _ _ _ _


theorem ror_r32_imm8_step [Bindings] (s : RamState) (h : ReadyToStep s) (modrm imm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1)
    (hcode : BytesAt s s.RIP [0xC1, modrm, imm]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    let dst : Operand 32 := .reg (gprNumber 0 0 (modrmRm modrm))
    let c := shiftCount 32 imm.toBitVec
    X86.Machine.step s = some (.next (afterStep s 3 fun t =>
      writeOutputs t dst (rorSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) c (dst.read t))
        (rorOracleBits c) (BitVec.add s.RIP 3#64))) := by
  have hdecode := decodeLegacy0_run_of_C1_ror s h modrm imm hmod hreg hcode hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have himm : (Mem_Fetch (BitVec.add s.RIP 2#64) 8).run (afterFetches (beforeFetch s) 3) =
      (.ok imm.toBitVec, afterFetches (beforeFetch s) 4) :=
    memFetch_run_of_bytesAt (beforeFetch s) 3 h.fetchReady hcode hlow 2 (by simp) (by decide)
  rw [ror_r_imm8_form _ _ _ _ _ _ (hmode 3) himm (hmode 4) 32 (by decide)
    (legacyContext_operand_size s.DS) rfl,
    show BitVec.add (BitVec.add s.RIP 2#64) 1#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc s.RIP 2#64 1#64] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0xC1 [modrm, imm]
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode ((hmode 4).of_cs_lma_eq rfl rfl)


theorem ror_r32_imm8_ready [Bindings] {s : RamState} (h : ReadyToStep s)
    (modrm imm : UInt8) :
    let dst : Operand 32 := .reg (gprNumber 0 0 (modrmRm modrm))
    let c := shiftCount 32 imm.toBitVec
    ReadyToStep (afterStep s 3 fun t =>
      writeOutputs t dst (rorSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) c (dst.read t))
        (rorOracleBits c) (BitVec.add s.RIP 3#64)) :=
  ReadyToStep.afterStep_writeOutputs h 3 _ _ _ _


theorem ror_r32_imm8_rex_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex modrm imm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1)
    (hcode : BytesAt s s.RIP [rex, 0xC1, modrm, imm]) (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    let dst : Operand 32 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    let c := shiftCount 32 imm.toBitVec
    X86.Machine.step s = some (.next (afterStep s 4 fun t =>
      writeOutputs t dst (rorSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) c (dst.read t))
        (rorOracleBits c) (BitVec.add s.RIP 4#64))) := by
  have hdecode := decodeLegacy0_run_of_rex_C1_ror s h rex modrm imm hmod hreg hcode hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have himm : (Mem_Fetch (BitVec.add s.RIP 3#64) 8).run (afterFetches (beforeFetch s) 4) =
      (.ok imm.toBitVec, afterFetches (beforeFetch s) 5) :=
    memFetch_run_of_bytesAt (beforeFetch s) 4 h.fetchReady hcode hlow 3 (by simp) (by decide)
  rw [ror_r_imm8_form _ _ _ _ _ _ (hmode 4) himm (hmode 5) 32 (by decide)
    (hrex.operand_size s.DS) rfl,
    show BitVec.add (BitVec.add s.RIP 3#64) 1#64 = BitVec.add s.RIP 4#64 from
      BitVec.add_assoc s.RIP 3#64 1#64] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h rex 0xC1 [modrm, imm] hrex.rexPrefix
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode ((hmode 5).of_cs_lma_eq rfl rfl)


theorem ror_r32_imm8_rex_ready [Bindings] {s : RamState} (h : ReadyToStep s)
    (rex modrm imm : UInt8) :
    let dst : Operand 32 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    let c := shiftCount 32 imm.toBitVec
    ReadyToStep (afterStep s 4 fun t =>
      writeOutputs t dst (rorSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) c (dst.read t))
        (rorOracleBits c) (BitVec.add s.RIP 4#64)) :=
  ReadyToStep.afterStep_writeOutputs h 4 _ _ _ _


theorem ror_r64_one_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1)
    (hcode : BytesAt s s.RIP [rex, 0xD1, modrm]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    let dst : Operand 64 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s 3 fun t =>
      writeOutputs t dst (rorSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) 1 (dst.read t))
        (rorOracleBits 1) (BitVec.add s.RIP 3#64))) := by
  have hdecode := decodeLegacy0_run_of_rex_D1_ror s h rex modrm hmod hreg hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 4) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [ror_r_one_form _ _ _ _ hmode 64 (by decide)
    (hrex.operand_size s.DS) rfl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h rex 0xD1 [modrm] hrex.rexPrefix
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode (hmode.of_cs_lma_eq rfl rfl)


theorem ror_r64_one_ready [Bindings] {s : RamState} (h : ReadyToStep s)
    (rex modrm : UInt8) :
    let dst : Operand 64 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    ReadyToStep (afterStep s 3 fun t =>
      writeOutputs t dst (rorSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) 1 (dst.read t))
        (rorOracleBits 1) (BitVec.add s.RIP 3#64)) :=
  ReadyToStep.afterStep_writeOutputs h 3 _ _ _ _


theorem ror_r32_one_step [Bindings] (s : RamState) (h : ReadyToStep s) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1)
    (hcode : BytesAt s s.RIP [0xD1, modrm]) (hlow : s.RIP.toNat + 2 ≤ 2^32) :
    let dst : Operand 32 := .reg (gprNumber 0 0 (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s 2 fun t =>
      writeOutputs t dst (rorSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) 1 (dst.read t))
        (rorOracleBits 1) (BitVec.add s.RIP 2#64))) := by
  have hdecode := decodeLegacy0_run_of_D1_ror s h modrm hmod hreg hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 3) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [ror_r_one_form _ _ _ _ hmode 32 (by decide)
    (legacyContext_operand_size s.DS) rfl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0xD1 [modrm]
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode (hmode.of_cs_lma_eq rfl rfl)


theorem ror_r32_one_ready [Bindings] {s : RamState} (h : ReadyToStep s)
    (modrm : UInt8) :
    let dst : Operand 32 := .reg (gprNumber 0 0 (modrmRm modrm))
    ReadyToStep (afterStep s 2 fun t =>
      writeOutputs t dst (rorSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) 1 (dst.read t))
        (rorOracleBits 1) (BitVec.add s.RIP 2#64)) :=
  ReadyToStep.afterStep_writeOutputs h 2 _ _ _ _


theorem ror_r32_one_rex_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1)
    (hcode : BytesAt s s.RIP [rex, 0xD1, modrm]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    let dst : Operand 32 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s 3 fun t =>
      writeOutputs t dst (rorSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) 1 (dst.read t))
        (rorOracleBits 1) (BitVec.add s.RIP 3#64))) := by
  have hdecode := decodeLegacy0_run_of_rex_D1_ror s h rex modrm hmod hreg hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 4) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [ror_r_one_form _ _ _ _ hmode 32 (by decide)
    (hrex.operand_size s.DS) rfl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h rex 0xD1 [modrm] hrex.rexPrefix
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode (hmode.of_cs_lma_eq rfl rfl)


theorem ror_r32_one_rex_ready [Bindings] {s : RamState} (h : ReadyToStep s)
    (rex modrm : UInt8) :
    let dst : Operand 32 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    ReadyToStep (afterStep s 3 fun t =>
      writeOutputs t dst (rorSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) 1 (dst.read t))
        (rorOracleBits 1) (BitVec.add s.RIP 3#64)) :=
  ReadyToStep.afterStep_writeOutputs h 3 _ _ _ _

end X86Proofs
