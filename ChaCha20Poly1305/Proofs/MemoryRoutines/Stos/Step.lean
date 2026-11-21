import ChaCha20Poly1305.Proofs.MemoryRoutines.Stos.Decode

namespace ChaCha20Poly1305.Proofs.MemoryRoutines.Stos

open X86 X86.Machine X86.UserProcess X86Proofs

theorem step_stos_of_decode [Bindings] (kind : Kind) (s t : RamState) (h : ReadyMidRep s)
    (hcode : BytesAt s s.RIP kind.code) (hlow : s.RIP.toNat + kind.code.length ≤ 2^32)
    (hdecode : (X86.Helpers.Decode_Legacy_0
        (BitVec.add s.RIP (BitVec.ofNat 64 (kind.code.length - 1))) (kind.context s.DS)).run
        (afterFetches (beforeFetch s) kind.code.length) = some (.ok (), t))
    (hmode : In64BitMode t) : X86.Machine.step s = some (.next (finishStep t)) := by
  cases kind with
  | byte =>
    exact step_f3_legacy0_midRep s t h 0xaa
      (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow (by rfl) hdecode hmode
  | qword =>
    exact step_f3_rex_legacy0 s t h 0x48 0xab []
      (RexWPrefix.rexPrefix (by simp [RexWPrefix])) (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode hmode

theorem rep_stos_step [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (kind : Kind) (s : RamState) (h : ReadyMidRep s)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP kind.code)
    (hlow : s.RIP.toNat + kind.code.length ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hdst : (rdi.read s).toNat + kind.bytes ≤ 2^32)
    (_hdstPage : (rdi.read s).toNat % 4096 + kind.bytes ≤ 4096)
    (hdstMem : ∀ i < kind.bytes, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome) :
    X86.Machine.step s = some (.next (repStosAfter kind s)) := by
  have hdecode := decodeLegacy0_run_of_stos kind s h hcode hlow
  have hf := h.fetchReady
  let t := afterFetches (beforeFetch s) (kind.code.length + 1)
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have ht : DataReady t := h.dataReady.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [rep_stos_form hstride kind t _ _ ht hmode
    (by cases kind <;> rfl) (by cases kind <;> rfl) (by cases kind <;> rfl)
    (by rintro rfl; rfl) hcpu.es hdf hcount hdst hdstMem] at hdecode
  exact step_stos_of_decode kind s _ h hcode hlow hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem rep_stos_step_zero [Bindings] (kind : Kind) (s : RamState)
    (h : ReadyMidRep s) (hcode : BytesAt s s.RIP kind.code)
    (hlow : s.RIP.toNat + kind.code.length ≤ 2^32) (hcount : rcx.read s = 0) :
    X86.Machine.step s = some (.next (repStosZeroAfter kind s)) := by
  have hdecode := decodeLegacy0_run_of_stos kind s h hcode hlow
  have hf := h.fetchReady
  let t := afterFetches (beforeFetch s) (kind.code.length + 1)
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  rw [rep_stos_form_zero kind t _ _ (by cases kind <;> rfl) (by cases kind <;> rfl)
    (by cases kind <;> rfl) (by rintro rfl; rfl) hcount] at hdecode
  exact step_stos_of_decode kind s _ h hcode hlow hdecode (hmode.of_cs_lma_eq rfl rfl)

end ChaCha20Poly1305.Proofs.MemoryRoutines.Stos
