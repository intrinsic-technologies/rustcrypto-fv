import Hkdf.Proofs.Common.Encoding.Parser.LengthCheck.Decode
import Hkdf.Proofs.Common.Encoding.Parser.LengthCheck.Form
import Hkdf.Proofs.Common.Encoding.Parser.LengthCheck.Address
import X86Proofs.Instructions.MovLoad.Step
import X86Proofs.Program.Effect

set_option autoImplicit false

namespace Hkdf.Proofs.Common.Encoding.Parser.LengthCheck

open X86Proofs X86 X86.Machine X86.UserProcess X86.Helpers

theorem afterStep_loadFlags_rip [Bindings] {s : RamState} (h : ReadyToStep s)
    (len : Nat) (flags : RamState → StatusFlags) (next : BitVec 64) :
    (afterStep s len fun t => writeFlagsOutputs (dataAccess t "load") (flags t) 0 next).RIP =
      next := by
  simp [afterStep, finishStep, writeFlagsOutputs, setFlags, afterFetches, beforeFetch,
    resetStepFields, dataAccess, h.ready.repeatClear, h.ready.msr]

theorem ReadyToStep.afterStep_loadFlags [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) (f : RamState → StatusFlags) (nextIP : BitVec 64) :
    ReadyToStep (afterStep s length fun t => writeFlagsOutputs (dataAccess t "load") (f t) 0 nextIP) := by
  have hst : SameControls s (afterStep s length fun t => writeFlagsOutputs (dataAccess t "load") (f t) 0 nextIP) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hc := h.cpu
  have hr := h.ready
  exact ⟨⟨hc.cs, hc.ss, hc.ds, hc.es, hc.cpl, hc.cr0, hc.cr4, hc.efer, hc.maxPhysical, hc.early,
      reportsCPUFeature_of_sameControls hst hc.lam, reportsCPUFeature_of_sameControls hst hc.lass, hc.debug,
      hc.aet⟩,
    ⟨h.memory.cr3, h.memory.tables⟩,
    ⟨hr.event, hr.active, hr.sti, hr.movss, hr.singleStep, hr.taskSwitch, hr.breakpoint,
      hr.busLock, StatusFlags.trapFlagClear_store _ hr.tf, StatusFlags.resumeFlagClear_store _ hr.rf,
      hr.repeatClear, hr.msr⟩,
    smrrUnblocked_of_sameControls hst h.smrr, writeBackMemoryType_of_sameControls hst h.memoryType,
    h.features.of_sameControls hst⟩

theorem AgreesExcept.afterStep_loadFlags (s : RamState) (length : Nat) (f : RamState → StatusFlags)
    (nextIP : BitVec 64) :
    AgreesExcept [.flags, .rip] s
      (afterStep s length fun t => writeFlagsOutputs (dataAccess t "load") (f t) 0 nextIP) := by
  refine ⟨fun c hc _ => ?_, fun _ _ => rfl, ?_, fun _ h => h⟩
  · cases c with
    | reg r => rfl
    | flags => exact absurd (by simp) hc
    | rip => exact absurd (by simp) hc
    | mem addr len => exact fun _ _ => rfl
    | xmm x => exact Component.agrees_xmm_of_zmm rfl x
    | mxcsr => rfl
    | fpr x => exact Component.agrees_fpr_of_fp87 rfl x
    | fsw => rfl
    | fcc => rfl
    | ftw => rfl
    | fcw => rfl
    | fpuPtr => rfl
    | df => exact dfBit_store _ _
  · simp only [fixedPart, afterStep, finishStep, writeFlagsOutputs, setFlags, afterFetches, beforeFetch,
      resetStepFields, clearStatusFlags_store, dataAccess]

theorem cmp_r64_m64_step_of_address [Bindings] (s : RamState) (h : ReadyToStep s)
    (rex modrm : UInt8) (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm ≠ 3)
    (rest : List UInt8) (addr off : BitVec 64) (isStack isRip : Bool)
    (hcode : BytesAt s s.RIP (rex :: 0x3b :: modrm :: rest))
    (hlow : s.RIP.toNat + (3 + rest.length) ≤ 2^32)
    {baseUsesRsp : Bool} (hea : (Effective_Address 64 (rexContext s.DS rex.toBitVec) (modrmMod modrm)
      (modrmRm modrm) 1 (BitVec.add s.RIP 3#64)).run (afterFetches (beforeFetch s) 4) =
      (.ok (off, flatData isStack, BitVec.add s.RIP (BitVec.ofNat 64 (3 + rest.length)), isRip, baseUsesRsp),
        afterFetches (beforeFetch s) (3 + rest.length + 1)))
    (hrip : Handle_RIP_Relative_Address 64 isRip off
      (BitVec.add s.RIP (BitVec.ofNat 64 (3 + rest.length))) = .ok addr)
    (hread : MemReadable s addr 8) :
    X86.Machine.step s = some (.next (afterStep s (3 + rest.length) fun t =>
      writeFlagsOutputs (dataAccess t "load")
        (cmpSpec ((Operand.reg (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) :
          Operand 64).read t) ((Operand.mem addr : Operand 64).read t)) 0
        (BitVec.add s.RIP (BitVec.ofNat 64 (3 + rest.length))))) := by
  have hlow' : s.RIP.toNat + (rex :: 0x3b :: modrm :: rest).length ≤ 2^32 := by
    simp only [List.length_cons]
    omega
  have hd := decodeLegacy0_run_of_rex_3B_memory s h rex modrm hmod rest hcode hlow'
  let t := afterFetches (beforeFetch s) (3 + rest.length + 1)
  have hm : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have ht : DataReady t := h.dataReady.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl rfl rfl rfl rfl h.memory.tables
  erw [cmp_r64_m64_form _ t _ _ _ (modrmReg modrm) _ (hrex.operand_size _) rfl rfl
    _ _ _ _ _ hea hrip ht hm (hread.of_external_eq rfl)] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h rex 0x3b _ hrex.rexPrefix
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow' hd
    (hm.of_cs_lma_eq rfl rfl)

end Hkdf.Proofs.Common.Encoding.Parser.LengthCheck
