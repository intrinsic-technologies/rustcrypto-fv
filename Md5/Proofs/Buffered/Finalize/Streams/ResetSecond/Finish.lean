import Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Length
import Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Copy
import Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Compression

namespace Md5.Proofs.Buffered.Finalize.Streams.ResetSecond

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Block

theorem finish [Bindings] {variant : Variant} {boundary : ReturnBoundary} {message : ByteArray} {s : RamState}
    (hOutside : ¬ InProgram boundary.rip) (h : Padded message s variant) :
    ∃ t, Post variant.toKind boundary message s t := by
  obtain ⟨n, u, hn, hu, hcu, hl⟩ := Length.run hOutside h
  have hus := h.toStorage.of_agrees hl.agrees (Length.effect_rsp hl)
  have hup := Length.prefix_bytes h hl
  have hub := Length.buffer_bytes h hl
  have hul := Length.length_bytes h hl
  obtain ⟨m, v, hm, hv, hcv, hc⟩ := Copy.run (variant := variant) (kind := .finalBlock) hOutside hu hcu
    ⟨hus, by cases variant <;> exact hl.rip⟩
  have hvs := hus.of_agrees hc.agrees (Copy.effect_rsp hc)
  have hvb := Copy.buffer_bytes hc hub
  have hvsp : stackPtr v = stackPtr s := (Copy.effect_rsp hc).trans (Length.effect_rsp hl)
  have hvprefix : Bytes v.external (stackPtr v + BitVec.ofNat 64 variant.blockOffset) 56
      (fun i ↦ if message.size % 64 < 56 then (firstBlock message)[i]! else 0) := by
    rw [Copy.effect_rsp hc]
    intro i hi
    exact (Copy.effect_copy hus hc i hi).trans (hup i hi)
  have hvlength : Bytes v.external (stackPtr v + BitVec.ofNat 64 variant.blockOffset + 56) 8
      (storedByte (BitVec.ofNat 64 (message.size * 8))) := by
    rw [Copy.effect_rsp hc, BitVec.add_assoc]
    have hoff : BitVec.ofNat 64 variant.blockOffset + 56 =
        BitVec.ofNat 64 (variant.blockOffset + 56) := by
      cases variant <;> decide
    rw [hoff]
    change Bytes v.external (stackPtr u + BitVec.ofNat 64 (variant.blockOffset + 56)) 8 _
    intro i hi
    exact (Copy.finalBlock_length hc i hi).trans (hul i hi)
  have hlast := lastBlock_bytes message hvprefix hvlength
  have hinput : (⟨(stackPtr v).toNat + variant.blockOffset, (lastBlock message).size⟩ : MemoryRegion).HasBytes
      v.external (lastBlock message) := by
    have hb := hasBytes_of_bytes (bytes := lastBlock message)
      (by simpa only [size_lastBlock] using hlast)
    have haddr : (stackPtr v + BitVec.ofNat 64 variant.blockOffset).toNat = (stackPtr v).toNat + variant.blockOffset :=
      hvs.stackAddress (by cases variant <;> decide)
    rw [haddr] at hb
    exact hb
  obtain ⟨hdi, hsi, hdx⟩ := Copy.effect_arguments hc
  rw [← Copy.effect_rsp hc] at hdi hsi
  change v.regValue .rdi = _ at hdi
  change v.regValue .rsi = _ at hsi
  change v.regValue .rdx = _ at hdx
  have hp := hvs.compressCallPre (src := variant.blockOffset) (dst := variant.resultOffset)
    hsi hdi (by rw [hdx, size_lastBlock]; rfl)
    (by rw [size_lastBlock]; cases variant <;> decide) (by cases variant <;> decide)
    (by rw [size_lastBlock]; cases variant <;> decide) hinput hvb
  obtain ⟨t, ht⟩ := Compression.run (variant := variant) hp hv hcv hOutside
    (by cases variant <;> exact hc.rip)
  have hsu : Transition boundary s u variant := ⟨⟨n, hn⟩, Length.effect_agrees hl⟩
  have huv : Transition boundary u v variant := ⟨⟨m, hm⟩, Copy.transition_agrees hc⟩
  have hvt : Transition boundary v t variant := ⟨ht.advances, Compression.agrees hdi ht.agrees⟩
  have hst := (hsu.trans huv).trans hvt
  refine ⟨t, hst.advances, ht.ready, ht.code, ht.rip, ?_, hst.agrees⟩
  have hb := ht.output
  have haddr : (stackPtr v + BitVec.ofNat 64 variant.resultOffset).toNat = (stackPtr v).toNat + variant.resultOffset :=
    hvs.stackAddress (by cases variant <;> decide)
  simp only [Compress.outputRegion, registerRegion, hdi] at hb
  rw [haddr, hvsp] at hb
  cases variant <;>
    simpa only [Kind.resultRegion, Kind.resultOffset, Variant.toKind, Variant.resultOffset,
      messageDigest_paddedBuffer] using hb

end Md5.Proofs.Buffered.Finalize.Streams.ResetSecond
