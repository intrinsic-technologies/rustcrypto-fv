import Md5.Proofs.MemoryRoutines.Memcpy.Body

namespace Md5.Proofs.MemoryRoutines

open X86 X86.Machine X86.UserProcess X86Proofs Md5.Spec.Program Md5.Proofs.Block

theorem memcpy_returns [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (s : RamState) (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hp : MemcpyPre s) :
    ∃ fuel t, Returns (returnBoundary s) fuel s t ∧ MemcpyResult s t := by
  obtain ⟨fuel, t, hrun, hbody, hcode, hip, hcopy⟩ :=
    memcpy_body hstride (returnBoundary s) hp.returnOutside s hr hc hp
  obtain ⟨u, hu, hresult, hext⟩ := call_body_returns hp.toCallPre hbody
    (program_text_slice hcode 0x24de 1 (by decide +kernel)) hip hrun
  exact ⟨fuel + 1, u, hu, ⟨hresult, fun i hi ↦ by rw [hext]; exact hcopy i hi⟩⟩

theorem memcpy_advances [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x1024b0 ∨ 0x1024df ≤ boundary.rip.toNat)
    (s : RamState) (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hp : MemcpyPre s) (hne : (returnBoundary s).rip ≠ boundary.rip) :
    ∃ fuel t, Advances boundary fuel s t ∧ MemcpyResult s t := by
  obtain ⟨fuel, t, hrun, hbody, hcode, hip, hcopy⟩ :=
    memcpy_body hstride boundary hb s hr hc hp
  obtain ⟨u, hu, hresult, hext⟩ := call_body_advances hp.toCallPre hbody
    (program_text_slice hcode 0x24de 1 (by decide +kernel)) hip hrun hne
  exact ⟨fuel + 1, u, hu, ⟨hresult, fun i hi ↦ by rw [hext]; exact hcopy i hi⟩⟩

end Md5.Proofs.MemoryRoutines
