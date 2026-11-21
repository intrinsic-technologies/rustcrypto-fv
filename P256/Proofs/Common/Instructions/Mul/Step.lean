import X86Proofs.Step.LegacyStep
import P256.Proofs.Common.Instructions.Mul.Form
import P256.Proofs.Common.Instructions.Mul.Decode

set_option autoImplicit false

open X86Proofs

namespace P256.Proofs.Common.Instructions

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem mul_r64_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4)
    (hcode : BytesAt s s.RIP [rex, 0xF7, modrm]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    let src := gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)
    X86.Machine.step s = some (.next (afterStep s 3 fun t =>
      mulResult64 {t with Next_IP := BitVec.add s.RIP 3#64} t.GPR[gprIndex src])) := by
  have hdecode := decodeLegacy0_run_of_rex_F7_mul s h rex modrm hmod hreg hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 4) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [mul_r64_form _ _ _ _ hmode (hrex.operand_size s.DS) rfl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h rex 0xF7 [modrm] hrex.rexPrefix
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode
    (hmode.of_cs_lma_eq rfl rfl)

theorem mul_r64_ready [Bindings] {s : RamState} (h : ReadyToStep s) (src : BitVec 5) :
    ReadyToStep (afterStep s 3 fun t =>
      mulResult64 {t with Next_IP := BitVec.add s.RIP 3#64} t.GPR[gprIndex src]) := by
  have hst : SameControls s (afterStep s 3 fun t =>
      mulResult64 {t with Next_IP := BitVec.add s.RIP 3#64} t.GPR[gprIndex src]) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hc := h.cpu
  have hr := h.ready
  exact ⟨⟨hc.cs, hc.ss, hc.ds, hc.es, hc.cpl, hc.cr0, hc.cr4, hc.efer, hc.maxPhysical, hc.early,
      reportsCPUFeature_of_sameControls hst hc.lam, reportsCPUFeature_of_sameControls hst hc.lass,
      hc.debug, hc.aet⟩,
    ⟨h.memory.cr3, h.memory.tables⟩,
    ⟨hr.event, hr.active, hr.sti, hr.movss, hr.singleStep, hr.taskSwitch, hr.breakpoint,
      hr.busLock, StatusFlags.trapFlagClear_store _ hr.tf, StatusFlags.resumeFlagClear_store _ hr.rf,
      hr.repeatClear, hr.msr⟩,
    smrrUnblocked_of_sameControls hst h.smrr, writeBackMemoryType_of_sameControls hst h.memoryType,
    h.features.of_sameControls hst⟩

end P256.Proofs.Common.Instructions
