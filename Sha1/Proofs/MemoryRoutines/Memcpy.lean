import Sha1.Proofs.MemoryRoutines.Memcpy.Body

namespace Sha1.Proofs.MemoryRoutines

open X86 X86.Machine X86.UserProcess X86Proofs Sha1.Spec.Program Sha1.Proofs.Compress.Machine

theorem memcpy_returns [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (s : RamState) (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hp : MemcpyPre s) :
    ∃ fuel t, Returns (returnBoundary s) fuel s t ∧ MemcpyResult s t := by
  obtain ⟨fuel, t, hrun, hbody, hcode, hip, hcopy⟩ :=
    memcpy_body hstride (returnBoundary s) hp.returnOutside s hr hc hp
  obtain ⟨u, hu, hresult, hext⟩ := call_body_returns hp.toCallPre hbody
    (program_text_slice hcode 0x375e 1 (by decide +kernel)) hip hrun
  exact ⟨fuel + 1, u, hu, ⟨hresult, fun i hi ↦ by rw [hext]; exact hcopy i hi⟩⟩

theorem memcpy_advances [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x103730 ∨ 0x10375f ≤ boundary.rip.toNat)
    (s : RamState) (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hp : MemcpyPre s) (hne : (returnBoundary s).rip ≠ boundary.rip) :
    ∃ fuel t, Advances boundary fuel s t ∧ MemcpyResult s t := by
  obtain ⟨fuel, t, hrun, hbody, hcode, hip, hcopy⟩ :=
    memcpy_body hstride boundary hb s hr hc hp
  obtain ⟨u, hu, hresult, hext⟩ := call_body_advances hp.toCallPre hbody
    (program_text_slice hcode 0x375e 1 (by decide +kernel)) hip hrun hne
  exact ⟨fuel + 1, u, hu, ⟨hresult, fun i hi ↦ by rw [hext]; exact hcopy i hi⟩⟩

end Sha1.Proofs.MemoryRoutines
