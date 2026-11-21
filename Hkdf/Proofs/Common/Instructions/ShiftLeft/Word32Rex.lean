import Hkdf.Proofs.Common.Instructions.ShiftLeft.Word32

set_option autoImplicit false

namespace Hkdf.Proofs.Common.Instructions.ShiftLeft

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem shl_r32_imm8_rex_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex modrm imm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4)
    (hcode : BytesAt s s.RIP [rex, 0xC1, modrm, imm]) (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    let dst : Operand 32 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    let c := shiftCount 32 imm.toBitVec
    X86.Machine.step s = some (.next (afterStep s 4 fun t =>
      writeOutputs t dst (shlSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (shlOracleAF t.oracle c) c (dst.read t))
        (shlOracleBits c) (BitVec.add s.RIP 4#64))) := by
  have hdecode := decodeLegacy0_run_of_rex_C1_shl s h rex modrm imm hmod hreg hcode hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have himm : (Mem_Fetch (BitVec.add s.RIP 3#64) 8).run (afterFetches (beforeFetch s) 4) =
      (.ok imm.toBitVec, afterFetches (beforeFetch s) 5) :=
    memFetch_run_of_bytesAt (beforeFetch s) 4 h.fetchReady hcode hlow 3 (by simp) (by decide)
  rw [shl_r_imm8_form _ _ _ _ _ _ (hmode 4) himm (hmode 5) 32 (by decide)
    (hrex.operand_size s.DS) rfl,
    show BitVec.add (BitVec.add s.RIP 3#64) 1#64 = BitVec.add s.RIP 4#64 from
      BitVec.add_assoc s.RIP 3#64 1#64] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h rex 0xC1 [modrm, imm] hrex.rexPrefix
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode ((hmode 5).of_cs_lma_eq rfl rfl)

theorem shl_r32_imm8_rex_ready [Bindings] {s : RamState} (h : ReadyToStep s)
    (rex modrm imm : UInt8) :
    let dst : Operand 32 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    let c := shiftCount 32 imm.toBitVec
    ReadyToStep (afterStep s 4 fun t =>
      writeOutputs t dst (shlSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (shlOracleAF t.oracle c) c (dst.read t))
        (shlOracleBits c) (BitVec.add s.RIP 4#64)) :=
  ReadyToStep.afterStep_writeOutputs h 4 _ _ _ _


theorem shl_r32_imm8_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm imm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xC1, modrm, imm])
      (shlR32Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (shiftCount 32 imm.toBitVec)) := by
  rintro s h hcode rfl
  refine ⟨_, shl_r32_imm8_rex_step s h rex modrm imm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), shl_r32_imm8_rex_ready h rex modrm imm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, shlSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply shlFlags_allows

end Hkdf.Proofs.Common.Instructions.ShiftLeft
