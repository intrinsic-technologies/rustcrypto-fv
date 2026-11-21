import X86Proofs.Step.AfterStep
import X86Proofs.Step.LegacyStep
import Sha3.Proofs.X86.Instructions.Cmp.Decode
import Sha3.Proofs.X86.Instructions.Cmp.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem cmp_r64_r64_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP [rex, 0x39, modrm]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    let dst : Operand 64 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    let src : Operand 64 := .reg (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
    X86.Machine.step s = some (.next (afterStep s 3 fun t =>
      writeFlagsOutputs t (cmpSpec (dst.read t) (src.read t)) 0
        (BitVec.add s.RIP 3#64))) := by
  have hdecode := decodeLegacy0_run_of_rex_39 s h rex modrm hmod hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 4) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [cmp_r_r_form _ _ _ _ _ hmode 64 (by decide)
    (hrex.operand_size s.DS) rfl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h rex 0x39 [modrm] hrex.rexPrefix
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem cmp_r64_r64_ready [Bindings] {s : RamState} (h : ReadyToStep s) (rex modrm : UInt8) :
    let dst : Operand 64 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    let src : Operand 64 := .reg (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
    ReadyToStep (afterStep s 3 fun t =>
      writeFlagsOutputs t (cmpSpec (dst.read t) (src.read t)) 0
        (BitVec.add s.RIP 3#64)) :=
  ReadyToStep.afterStep_writeFlagsOutputs h 3 _ 0 _

theorem cmp_r32_r32_step [Bindings] (s : RamState) (h : ReadyToStep s) (modrm : UInt8)
    (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP [0x39, modrm]) (hlow : s.RIP.toNat + 2 ≤ 2^32) :
    let dst : Operand 32 := .reg (gprNumber 0 0 (modrmRm modrm))
    let src : Operand 32 := .reg (gprNumber 0 0 (modrmReg modrm))
    X86.Machine.step s = some (.next (afterStep s 2 fun t =>
      writeFlagsOutputs t (cmpSpec (dst.read t) (src.read t)) 0
        (BitVec.add s.RIP 2#64))) := by
  have hdecode := decodeLegacy0_run_of_39 s h modrm hmod hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 3) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [cmp_r_r_form _ _ _ _ _ hmode 32 (by decide)
    (legacyContext_operand_size s.DS) rfl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0x39 [modrm]
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem cmp_r32_r32_ready [Bindings] {s : RamState} (h : ReadyToStep s) (modrm : UInt8) :
    let dst : Operand 32 := .reg (gprNumber 0 0 (modrmRm modrm))
    let src : Operand 32 := .reg (gprNumber 0 0 (modrmReg modrm))
    ReadyToStep (afterStep s 2 fun t =>
      writeFlagsOutputs t (cmpSpec (dst.read t) (src.read t)) 0
        (BitVec.add s.RIP 2#64)) :=
  ReadyToStep.afterStep_writeFlagsOutputs h 2 _ 0 _

theorem cmp_r32_r32_rex_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP [rex, 0x39, modrm]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    let dst : Operand 32 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    let src : Operand 32 := .reg (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
    X86.Machine.step s = some (.next (afterStep s 3 fun t =>
      writeFlagsOutputs t (cmpSpec (dst.read t) (src.read t)) 0
        (BitVec.add s.RIP 3#64))) := by
  have hdecode := decodeLegacy0_run_of_rex_39 s h rex modrm hmod hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 4) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [cmp_r_r_form _ _ _ _ _ hmode 32 (by decide)
    (hrex.operand_size s.DS) rfl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h rex 0x39 [modrm] hrex.rexPrefix
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem cmp_r32_r32_rex_ready [Bindings] {s : RamState} (h : ReadyToStep s) (rex modrm : UInt8) :
    let dst : Operand 32 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    let src : Operand 32 := .reg (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
    ReadyToStep (afterStep s 3 fun t =>
      writeFlagsOutputs t (cmpSpec (dst.read t) (src.read t)) 0
        (BitVec.add s.RIP 3#64)) :=
  ReadyToStep.afterStep_writeFlagsOutputs h 3 _ 0 _

end X86Proofs
