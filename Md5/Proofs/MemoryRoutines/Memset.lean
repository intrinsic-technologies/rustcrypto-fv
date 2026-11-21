import Md5.Proofs.MemoryRoutines.Memset.Prefix

namespace Md5.Proofs.MemoryRoutines

open X86 X86.Machine X86.UserProcess X86Proofs Md5.Spec.Program Md5.Proofs.Block

theorem memset_body [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (boundary : ReturnBoundary) (hb : Memset.Outside boundary)
    (s : RamState) (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hp : MemsetPre s) :
    ∃ fuel t, Advances boundary fuel s t ∧ CallBodyResult s t ∧
      CodeIn Extracted.programImage t ∧ t.RIP = 0x1024a4 ∧
      ∀ i < (rdx.read s).toNat, t.external[rdi.read s + BitVec.ofNat 64 i]? =
        some (UInt8.ofBitVec ((rsi.read s).setWidth 8)) := by
  obtain ⟨n₁, u, ha₁, hu⟩ := Memset.prepare boundary hb s hr hc hp
  obtain ⟨n₂, v, ha₂, hv, hipv⟩ := Memset.stores_run hstride boundary hb u
    (rdx.read s).toNat hu.ready hu.code hu.stores
  have hmove : StepEffect (fun t ↦ t.RIP = 0x1024a1)
      (codeRange 0x1024a1 [0x48, 0x89, 0xd0]) (movR64R64Effect 0x1024a1 0 2) :=
    mov_r64_r64_effect_step 0x1024a1 0x48 0xd0 (by unfold RexWPrefix; decide) (by decide)
  obtain ⟨t, ha₃, hrt, het⟩ := hmove.advances hv.ready
    (program_text_slice hv.code 0x24a1 3 (by decide +kernel)) hipv
    (hb.ne (p := 0x1024a4) (by decide) (by decide))
  have hct := het.agrees.codeIn (by simp [Component.Covers]) hv.code
  have hbody : CallBodyResult s t := by
    refine ⟨hrt, ?_, ?_, ?_⟩
    · exact (het.agrees.read (r := 4) (n := 64) (by simp)).trans
        ((hv.agrees.read (r := 4) (n := 64) (by simp [Memset.storeChanges])).trans hu.rsp)
    · exact het.writes.trans
        ((hv.agrees.read (r := 2) (n := 64) (by simp [Memset.storeChanges])).trans hu.saved)
    · apply ((hu.agrees.trans hv.agrees).trans het.agrees).mono
      simp [Memset.storeChanges, callChanges, hu.destination]
  refine ⟨n₁ + n₂ + 1, t, (ha₁.trans ha₂).trans ha₃, hbody, hct, het.rip, ?_⟩
  intro i hi
  have hfill := hv.fill i hi
  rw [hu.destination, hu.byte] at hfill
  exact (het.agrees.byte (by simp [Component.Covers])).trans hfill

theorem memset_returns [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (s : RamState) (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hp : MemsetPre s) :
    ∃ fuel t, Returns (returnBoundary s) fuel s t ∧ MemsetResult s t := by
  obtain ⟨fuel, t, hrun, hbody, hcode, hip, hfill⟩ :=
    memset_body hstride (returnBoundary s) hp.returnOutside s hr hc hp
  obtain ⟨u, hu, hresult, hext⟩ := call_body_returns hp hbody
    (program_text_slice hcode 0x24a4 1 (by decide +kernel)) hip hrun
  exact ⟨fuel + 1, u, hu, ⟨hresult, fun i hi ↦ by rw [hext]; exact hfill i hi⟩⟩

theorem memset_advances [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x102460 ∨ 0x1024a5 ≤ boundary.rip.toNat)
    (s : RamState) (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hp : MemsetPre s) (hne : (returnBoundary s).rip ≠ boundary.rip) :
    ∃ fuel t, Advances boundary fuel s t ∧ MemsetResult s t := by
  obtain ⟨fuel, t, hrun, hbody, hcode, hip, hfill⟩ :=
    memset_body hstride boundary hb s hr hc hp
  obtain ⟨u, hu, hresult, hext⟩ := call_body_advances hp hbody
    (program_text_slice hcode 0x24a4 1 (by decide +kernel)) hip hrun hne
  exact ⟨fuel + 1, u, hu, ⟨hresult, fun i hi ↦ by rw [hext]; exact hfill i hi⟩⟩

end Md5.Proofs.MemoryRoutines
