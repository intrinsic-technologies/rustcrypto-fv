import ChaCha20Poly1305.Proofs.MemoryRoutines.Movsb.Form
import ChaCha20Poly1305.Proofs.MemoryRoutines.Movsb.Decode
import ChaCha20Poly1305.Proofs.MemoryRoutines.Movsb.State
import ChaCha20Poly1305.Proofs.MemoryRoutines.Stos.Decode

namespace ChaCha20Poly1305.Proofs.MemoryRoutines.Movsb

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem rep_movsb_step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (s : RamState)
    (h : ReadyMidRep s) (hdf : DirectionFlagClear s.RFLAGS)
    (hcode : BytesAt s s.RIP [0xF3, 0xA4]) (hlow : s.RIP.toNat + 2 ≤ 2^32)
    (hcount : rcx.read s ≠ 0) (hsrc : (rsi.read s).toNat + 1 ≤ 2^32)
    (hdst : (rdi.read s).toNat + 1 ≤ 2^32)
    (hsrcMem : ∀ i < 1, (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome)
    (hdstMem : ∀ i < 1, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome) :
    X86.Machine.step s = some (.next (repMovsbAfter s)) := by
  have hdecode := decodeLegacy0_run_of_F3_A4 s h hcode hlow
  have hf := h.fetchReady
  let t := afterFetches (beforeFetch s) 3
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment (s := t) hf.cs hf.efer.lma
  have ht : DataReady t := h.dataReady.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [rep_movsb_form hstride t _ _ ht hmode rfl rfl rfl rfl rfl hcpu.ds hcpu.es
    hdf hcount hsrc hdst hsrcMem hdstMem] at hdecode
  exact Stos.step_f3_legacy0_midRep s _ h 0xA4
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow (by rfl) hdecode
    (hmode.of_cs_lma_eq rfl rfl)

theorem rep_movsb_step_zero [Bindings] (s : RamState) (h : ReadyMidRep s)
    (hcode : BytesAt s s.RIP [0xF3, 0xA4]) (hlow : s.RIP.toNat + 2 ≤ 2^32)
    (hcount : rcx.read s = 0) :
    X86.Machine.step s = some (.next (repMovsbZeroAfter s)) := by
  have hdecode := decodeLegacy0_run_of_F3_A4 s h hcode hlow
  have hf := h.fetchReady
  let t := afterFetches (beforeFetch s) 3
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment (s := t) hf.cs hf.efer.lma
  rw [rep_movsb_form_zero t _ _ rfl rfl rfl hcount] at hdecode
  exact Stos.step_f3_legacy0_midRep s _ h 0xA4
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow (by rfl) hdecode
    (hmode.of_cs_lma_eq rfl rfl)

end ChaCha20Poly1305.Proofs.MemoryRoutines.Movsb
