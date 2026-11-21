import Md5.Proofs.Buffered.Finalize.Streams.Slices.LengthBytes
import Md5.Proofs.Buffered.Finalize.Streams.Slices.Blocks.Copy.Properties

namespace Md5.Proofs.Buffered.Finalize.Streams.Slices

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem lastBlock_ready {update : Bool} [Bindings] {message : ByteArray} {s u t : RamState}
    (h : LengthReady (update := update) message s) (hl : (Blocks.Length.effect (update := update) s).Holds s u)
    (hc : (Blocks.Copy.effect (update := update) .finalBlock u).Holds u t)
    (ht : ReadyToStep t) (hct : CodeIn Extracted.programImage t) : CallReady (update := update) message t := by
  cases update
  case' false => let update := false
  case' true => let update := true
  all_goals
    have hus := h.toStorage.of_agrees hl.agrees (Blocks.Length.effect_rsp hl)
    have hts := hus.of_agrees hc.agrees (Blocks.Copy.effect_rsp hc)
    have hp := LengthBytes.prefix_bytes h hl
    have hb := Blocks.Copy.buffer_bytes hc (LengthBytes.buffer_bytes h hl)
    have hlen := LengthBytes.length_bytes h hl
    have hprefix : Bytes t.external (stackPtr t + 104) 56
        (fun i ↦ if message.size % 64 < 56 then (firstBlock message)[i]! else 0) := by
      rw [Blocks.Copy.effect_rsp hc]
      intro i hi
      exact (Blocks.Copy.effect_copy hus hc i hi).trans (hp i hi)
    have hlength : Bytes t.external (stackPtr t + 104 + 56) 8
        (storedByte (BitVec.ofNat 64 (message.size * 8))) := by
      rw [Blocks.Copy.effect_rsp hc, BitVec.add_assoc]
      change Bytes t.external (stackPtr u + 160) 8 _
      intro i hi
      exact (Blocks.Copy.finalBlock_length hc i hi).trans (hlen i hi)
    have hlast := lastBlock_bytes message hprefix hlength
    have hinput : (⟨(stackPtr t).toNat + 104, 64⟩ : MemoryRegion).HasBytes
        t.external (lastBlock message) := by
      have hb := hasBytes_of_bytes (bytes := lastBlock message)
        (by simpa only [size_lastBlock] using hlast)
      change (⟨(stackPtr t + BitVec.ofNat 64 104).toNat, (lastBlock message).size⟩ :
        MemoryRegion).HasBytes t.external (lastBlock message) at hb
      rw [hts.stackAddress (by decide : 104 ≤ 280), size_lastBlock] at hb
      exact hb
    obtain ⟨hdi, hsi, hdx⟩ := Blocks.Copy.effect_arguments hc
    rw [← Blocks.Copy.effect_rsp hc] at hdi hsi
    exact ⟨hts, ht, hct, hc.rip, hinput, hb, hsi, hdi, hdx⟩

end Md5.Proofs.Buffered.Finalize.Streams.Slices
