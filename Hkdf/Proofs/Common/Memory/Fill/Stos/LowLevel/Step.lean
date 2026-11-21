import Hkdf.Proofs.Common.Memory.Fill.Stos.LowLevel.Form
import Hkdf.Proofs.Common.Memory.Fill.Stos.LowLevel.Decode

open Hkdf.Proofs.Common.Memory.Copy.Movsb (step_f3_legacy0_midRep)

namespace Hkdf.Proofs.Common.Memory.Fill.Stos

open X86Proofs X86 X86.Machine X86.UserProcess X86.Helpers

theorem rep_stosb_step [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (s : RamState) (h : ReadyMidRep s) (hdf : DirectionFlagClear s.RFLAGS)
    (hcode : BytesAt s s.RIP [0xF3, 0xAA]) (hlow : s.RIP.toNat + 2 ≤ 2^32)
    (hcount : rcx.read s ≠ 0) (hdst : (rdi.read s).toNat + 1 ≤ 2^32)
    (hdstMem : ∀ i < 1, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome) :
    X86.Machine.step s = some (.next (repStosAfter 1 2 s)) := by
  have hdecode := decodeLegacy0_run_of_F3_AA s h hcode hlow
  have hf := h.fetchReady
  let t := afterFetches (beforeFetch s) 3
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment (s := t) hf.cs hf.efer.lma
  have ht : DataReady t := h.dataReady.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  have hform := rep_stos_form hstride 1 (.inl rfl) t (BitVec.add s.RIP 2#64)
    (repContext s.DS) ht hmode rfl rfl rfl (by intro he; contradiction)
    hcount hcpu.es hdf hdst hdstMem
  simp only [↓reduceIte] at hform
  rw [hform] at hdecode
  exact step_f3_legacy0_midRep s _ h 0xAA []
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow rfl hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem rep_stosq_step [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (s : RamState) (h : ReadyMidRep s) (hdf : DirectionFlagClear s.RFLAGS)
    (hcode : BytesAt s s.RIP [0xF3, 0x48, 0xAB]) (hlow : s.RIP.toNat + 3 ≤ 2^32)
    (hcount : rcx.read s ≠ 0) (hdst : (rdi.read s).toNat + 8 ≤ 2^32)
    (hdstMem : ∀ i < 8, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome) :
    X86.Machine.step s = some (.next (repStosAfter 8 3 s)) := by
  have hrex : RexWPrefix (0x48 : UInt8).toBitVec := by simp [RexWPrefix]
  have hdecode := decodeLegacy0_run_of_F3_rex_AB s h 0x48 hrex hcode hlow
  have hf := h.fetchReady
  let t := afterFetches (beforeFetch s) 4
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment (s := t) hf.cs hf.efer.lma
  have ht : DataReady t := h.dataReady.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  have hform := rep_stos_form hstride 8 (.inr rfl) t (BitVec.add s.RIP 3#64)
    (repRexContext s.DS (0x48 : UInt8).toBitVec) ht hmode rfl rfl rfl
    (fun _ => repRexContext_rex_w hrex _) hcount hcpu.es hdf hdst hdstMem
  simp only [show ¬ ((8 : Nat) = 1) from by decide, ↓reduceIte] at hform
  rw [hform] at hdecode
  have hstep := step_f3_rex_legacy0 s _ h 0x48 0xAB [] hrex.rexPrefix
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode (hmode.of_cs_lma_eq rfl rfl)
  rw [show scanPreservesRepeat (0xAB : UInt8).toBitVec (repRexContext s.DS (0x48 : UInt8).toBitVec)
    = true from rfl] at hstep
  exact hstep

theorem rep_stosb_step_zero [Bindings] (s : RamState) (h : ReadyMidRep s)
    (hcode : BytesAt s s.RIP [0xF3, 0xAA]) (hlow : s.RIP.toNat + 2 ≤ 2^32)
    (hcount : rcx.read s = 0) :
    X86.Machine.step s = some (.next (repStosZeroAfter 2 s)) := by
  have hdecode := decodeLegacy0_run_of_F3_AA s h hcode hlow
  have hf := h.fetchReady
  let t := afterFetches (beforeFetch s) 3
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment (s := t) hf.cs hf.efer.lma
  have hform := rep_stos_form_zero 1 (.inl rfl) t (BitVec.add s.RIP 2#64)
    (repContext s.DS) rfl rfl rfl (by intro he; contradiction) hcount
  simp only [↓reduceIte] at hform
  rw [hform] at hdecode
  exact step_f3_legacy0_midRep s _ h 0xAA []
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow rfl hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem rep_stosq_step_zero [Bindings] (s : RamState) (h : ReadyMidRep s)
    (hcode : BytesAt s s.RIP [0xF3, 0x48, 0xAB]) (hlow : s.RIP.toNat + 3 ≤ 2^32)
    (hcount : rcx.read s = 0) :
    X86.Machine.step s = some (.next (repStosZeroAfter 3 s)) := by
  have hrex : RexWPrefix (0x48 : UInt8).toBitVec := by simp [RexWPrefix]
  have hdecode := decodeLegacy0_run_of_F3_rex_AB s h 0x48 hrex hcode hlow
  have hf := h.fetchReady
  let t := afterFetches (beforeFetch s) 4
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment (s := t) hf.cs hf.efer.lma
  have hform := rep_stos_form_zero 8 (.inr rfl) t (BitVec.add s.RIP 3#64)
    (repRexContext s.DS (0x48 : UInt8).toBitVec) rfl rfl rfl
    (fun _ => repRexContext_rex_w hrex _) hcount
  simp only [show ¬ ((8 : Nat) = 1) from by decide, ↓reduceIte] at hform
  rw [hform] at hdecode
  have hstep := step_f3_rex_legacy0 s _ h 0x48 0xAB [] hrex.rexPrefix
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode (hmode.of_cs_lma_eq rfl rfl)
  rw [show scanPreservesRepeat (0xAB : UInt8).toBitVec (repRexContext s.DS (0x48 : UInt8).toBitVec)
    = true from rfl] at hstep
  exact hstep

end Hkdf.Proofs.Common.Memory.Fill.Stos
