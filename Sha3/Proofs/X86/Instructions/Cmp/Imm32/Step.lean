import X86Proofs.Step.AfterStep
import X86Proofs.Step.LegacyStep
import X86Proofs.Step.FetchImm
import Sha3.Proofs.X86.Instructions.Cmp.Imm32.Decode
import Sha3.Proofs.X86.Instructions.Cmp.Imm32.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem cmp_r64_imm32_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (rex modrm : UInt8) (imm : BitVec 32) (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 7)
    (hcode : BytesAt s s.RIP (rex :: 0x81 :: modrm :: immBytes 32 imm))
    (hlow : s.RIP.toNat + 7 ≤ 2^32) :
    let dst : Operand 64 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s 7 fun t =>
      writeFlagsOutputs t (cmpSpec (dst.read t) (imm.signExtend 64)) 0
        (BitVec.add s.RIP 7#64))) := by
  have hdecode := decodeLegacy0_run_of_rex_81_r7 s h rex modrm imm hmod hreg
    hcode hlow
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (rex :: 0x81 :: modrm :: immBytes 32 imm) := hcode
  have hlow' : s.RIP.toNat + (rex :: 0x81 :: modrm :: immBytes 32 imm).length ≤ 2^32 := by
    simpa using hlow
  have himm := memFetch_run_of_bytesAt_imm (beforeFetch s) 4 h.fetchReady hc hlow' 32 (by decide) imm 3
    (immBytes_getElem?_append [rex, 0x81, modrm] imm) (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [cmp_r_imm32_form _ _ (BitVec.add s.RIP 3#64) _ _ imm (hmode 4) 64 (by decide) (hrex.operand_size s.DS) rfl himm,
    show BitVec.add (BitVec.add s.RIP 3#64) 4#64 = BitVec.add s.RIP 7#64 from
      BitVec.add_assoc _ _ _] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h rex 0x81 (modrm :: immBytes 32 imm) hrex.rexPrefix
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow' hdecode ((hmode 8).of_cs_lma_eq rfl rfl)

theorem cmp_r64_imm32_ready [Bindings] {s : RamState} (h : ReadyToStep s) (rex modrm : UInt8) (imm : BitVec 32) :
    let dst : Operand 64 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    ReadyToStep (afterStep s 7 fun t =>
      writeFlagsOutputs t (cmpSpec (dst.read t) (imm.signExtend 64)) 0
        (BitVec.add s.RIP 7#64)) :=
  ReadyToStep.afterStep_writeFlagsOutputs h 7 _ 0 _

theorem cmp_r32_imm32_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (modrm : UInt8) (imm : BitVec 32) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 7)
    (hcode : BytesAt s s.RIP (0x81 :: modrm :: immBytes 32 imm))
    (hlow : s.RIP.toNat + 6 ≤ 2^32) :
    let dst : Operand 32 := .reg (gprNumber 0 0 (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s 6 fun t =>
      writeFlagsOutputs t (cmpSpec (dst.read t) (imm.signExtend 32)) 0
        (BitVec.add s.RIP 6#64))) := by
  have hdecode := decodeLegacy0_run_of_81_r7 s h modrm imm hmod hreg
    hcode hlow
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (0x81 :: modrm :: immBytes 32 imm) := hcode
  have hlow' : s.RIP.toNat + (0x81 :: modrm :: immBytes 32 imm).length ≤ 2^32 := by
    simpa using hlow
  have himm := memFetch_run_of_bytesAt_imm (beforeFetch s) 3 h.fetchReady hc hlow' 32 (by decide) imm 2
    (immBytes_getElem?_append [0x81, modrm] imm) (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [cmp_r_imm32_form _ _ (BitVec.add s.RIP 2#64) _ _ imm (hmode 3) 32 (by decide) (legacyContext_operand_size s.DS) rfl himm,
    show BitVec.add (BitVec.add s.RIP 2#64) 4#64 = BitVec.add s.RIP 6#64 from
      BitVec.add_assoc _ _ _] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0x81 (modrm :: immBytes 32 imm)
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow' hdecode ((hmode 7).of_cs_lma_eq rfl rfl)

theorem cmp_r32_imm32_ready [Bindings] {s : RamState} (h : ReadyToStep s) (modrm : UInt8) (imm : BitVec 32) :
    let dst : Operand 32 := .reg (gprNumber 0 0 (modrmRm modrm))
    ReadyToStep (afterStep s 6 fun t =>
      writeFlagsOutputs t (cmpSpec (dst.read t) (imm.signExtend 32)) 0
        (BitVec.add s.RIP 6#64)) :=
  ReadyToStep.afterStep_writeFlagsOutputs h 6 _ 0 _

theorem cmp_r32_imm32_rex_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (rex modrm : UInt8) (imm : BitVec 32) (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 7)
    (hcode : BytesAt s s.RIP (rex :: 0x81 :: modrm :: immBytes 32 imm))
    (hlow : s.RIP.toNat + 7 ≤ 2^32) :
    let dst : Operand 32 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s 7 fun t =>
      writeFlagsOutputs t (cmpSpec (dst.read t) (imm.signExtend 32)) 0
        (BitVec.add s.RIP 7#64))) := by
  have hdecode := decodeLegacy0_run_of_rex_81_r7 s h rex modrm imm hmod hreg
    hcode hlow
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (rex :: 0x81 :: modrm :: immBytes 32 imm) := hcode
  have hlow' : s.RIP.toNat + (rex :: 0x81 :: modrm :: immBytes 32 imm).length ≤ 2^32 := by
    simpa using hlow
  have himm := memFetch_run_of_bytesAt_imm (beforeFetch s) 4 h.fetchReady hc hlow' 32 (by decide) imm 3
    (immBytes_getElem?_append [rex, 0x81, modrm] imm) (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [cmp_r_imm32_form _ _ (BitVec.add s.RIP 3#64) _ _ imm (hmode 4) 32 (by decide) (hrex.operand_size s.DS) rfl himm,
    show BitVec.add (BitVec.add s.RIP 3#64) 4#64 = BitVec.add s.RIP 7#64 from
      BitVec.add_assoc _ _ _] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h rex 0x81 (modrm :: immBytes 32 imm) hrex.rexPrefix
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow' hdecode ((hmode 8).of_cs_lma_eq rfl rfl)

theorem cmp_r32_imm32_rex_ready [Bindings] {s : RamState} (h : ReadyToStep s) (rex modrm : UInt8) (imm : BitVec 32) :
    let dst : Operand 32 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    ReadyToStep (afterStep s 7 fun t =>
      writeFlagsOutputs t (cmpSpec (dst.read t) (imm.signExtend 32)) 0
        (BitVec.add s.RIP 7#64)) :=
  ReadyToStep.afterStep_writeFlagsOutputs h 7 _ 0 _

end X86Proofs
