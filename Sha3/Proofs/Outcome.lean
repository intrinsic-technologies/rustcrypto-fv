import Sha3.Spec.Program
import X86Proofs.Program.ReadWrite.Stack

namespace X86Proofs

open X86 X86.Machine Prelude

theorem SupportedSSE.of_sameControls [Bindings] {s t : RamState} (hst : SameControls s t)
    (h : Prelude.SupportedSSE Bindings.processor s) : Prelude.SupportedSSE Bindings.processor t :=
  ⟨reportsCPUFeature_of_sameControls hst h.feature, hst.cr0 ▸ h.cr0, hst.cr4 ▸ h.cr4⟩

theorem SameControls.of_fixedPart {s t : RamState} (h : fixedPart t = fixedPart s) :
    SameControls s t :=
  ⟨congrArg (·.XCR0) h, congrArg (·.CR0) h, congrArg (·.CR4) h,
    congrArg (·.IA32_PAT) h, congrArg (·.IA32_MTRR_DEF_TYPE) h,
    congrArg (·.MTRR_Fixed) h, congrArg (·.MTRR_Base) h, congrArg (·.MTRR_Mask) h,
    congrArg (·.IA32_SMRR_PHYSBASE) h, congrArg (·.IA32_SMRR_PHYSMASK) h,
    congrArg (·.«SMM::In_SMM») h⟩

theorem SupportedSSE.of_agreesExcept [Bindings] {cs : List Component} {s t : RamState}
    (h : AgreesExcept cs s t) (hs : Prelude.SupportedSSE Bindings.processor s) :
    Prelude.SupportedSSE Bindings.processor t :=
  SupportedSSE.of_sameControls (SameControls.of_fixedPart h.rest) hs

def WritesWithin (cs : List Component) (regions : Vector MemoryRegion n) : Prop :=
  ∀ c ∈ cs, ∀ address, c.Covers address →
    ∃ region ∈ regions, region.Contains address.toNat

theorem AgreesExcept.memoryWriteFrame {cs : List Component} {s t : RamState}
    {regions : Vector MemoryRegion n} (h : AgreesExcept cs s t)
    (hw : WritesWithin cs regions) : MemoryWriteFrame s t regions := by
  intro address hout
  apply h.byte
  intro c hc hcover
  obtain ⟨region, hr, hin⟩ := hw c hc address hcover
  exact hout region hr hin

theorem AgreesExcept.directionFlagClear {cs : List Component} {s t : RamState}
    (h : AgreesExcept cs s t) (hs : Prelude.RFLAGS.DirectionFlagClear s.RFLAGS)
    (hd : .df ∉ cs := by decide) : Prelude.RFLAGS.DirectionFlagClear t.RFLAGS :=
  ⟨(h.df hd).trans hs.df⟩

end X86Proofs

namespace Sha3.Proofs

open X86 X86.Machine X86Proofs Prelude Sha3.Spec.Program

theorem machineRamUnitStrideDecodable_of_ready [bindings : Bindings] {s : RamState}
    (hstride : UnitStringStride bindings) (h : ReadyToStep s) :
    MachineRamUnitStrideDecodable bindings s :=
  ⟨h.smrr, h.memoryType, hstride, h.features.lzcnt⟩

theorem supportedIntegerMachineState_of_ready [Bindings] {cs : List Component}
    {s t : RamState} (h : ReadyToStep t) (hframe : AgreesExcept cs s t)
    (hsse : Prelude.SupportedSSE Bindings.processor s) :
    SupportedIntegerMachineState Bindings.processor t :=
  ⟨h.cpu, X86Proofs.SupportedSSE.of_agreesExcept hframe hsse, h.memory, h.ready⟩

theorem calleeSavedRegistersUnchanged_of_agreesExcept {cs : List Component}
    {s t : RamState} (h : AgreesExcept cs s t)
    (hkeep : ∀ register ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15],
      Component.reg (BitVec.ofNat 5 register.fin.val) ∉ cs) :
    CalleeSavedRegistersUnchanged s t := by
  intro register hregister
  have he := h.agree (.reg (BitVec.ofNat 5 register.fin.val)) (hkeep register hregister) rfl
  have hr : (BitVec.ofNat 5 register.fin.val).toNat = register.fin.val := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    have := register.fin.isLt
    omega
  change t.GPR[(BitVec.ofNat 5 register.fin.val).toNat] =
    s.GPR[(BitVec.ofNat 5 register.fin.val).toNat] at he
  simpa only [hr, State.regValue] using he

theorem readBytes_eq_of_bytes {final : RamState} {region : MemoryRegion} {count : Nat}
    (digest : Vector UInt8 count)
    (hbytes : ∀ i : Fin count,
      final.external[BitVec.ofNat 64 (region.start + i.val)]? = some digest[i.val]) :
    readBytes region count final = .ok digest := by
  unfold readBytes
  simp only [hbytes]
  change Vector.ofFnM (fun i : Fin count ↦ pure digest[i.val]) =
    (pure digest : Except Machine.Fault (Vector UInt8 count))
  rw [Vector.ofFnM_pure, Vector.ofFn_getElem]

theorem readOutput_eq_of_bytes {initial final : RamState} {entry : Routine}
    (digest : Standards.NIST.SHA3.Digest entry.outputBytes)
    (hbytes : ∀ i : Fin entry.outputBytes,
      final.external[BitVec.ofNat 64 ((outputRegion entry initial).start + i.val)]? =
        some digest[i.val]) :
    readOutput entry initial final = .ok digest :=
  readBytes_eq_of_bytes digest hbytes

end Sha3.Proofs
