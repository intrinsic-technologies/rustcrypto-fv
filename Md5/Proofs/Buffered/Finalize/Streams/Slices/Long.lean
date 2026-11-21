import Md5.Proofs.Buffered.Finalize.Streams.Slices.Branches
import Md5.Proofs.Buffered.Finalize.Streams.Slices.Clear
import Md5.Proofs.Buffered.Finalize.Streams.Slices.Compression
import Md5.Proofs.Buffered.Finalize.Streams.Slices.Blocks.Copy

namespace Md5.Proofs.Buffered.Finalize.Streams.Slices

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem BranchReady.long {update : Bool} [Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {s : RamState} (hOutside : ¬ InProgram boundary.rip) (h : BranchReady (update := update) message s)
    (hLong : ¬ message.size % 64 < 56) :
    ∃ t, Transition (update := update) boundary s t ∧ LengthReady (update := update) message t := by
  cases update
  case' false => let update := false
  case' true => let update := true
  all_goals
    obtain ⟨n, u, hn, hu, hcu, hc⟩ := Blocks.Copy.run (update := update) (kind := .longTail)
      h.ready h.code h.toStorage hOutside (by simpa only [Blocks.Copy.Kind.entry, ite_eq_right hLong] using h.rip)
    have hus := h.toStorage.of_agrees hc.agrees (Blocks.Copy.effect_rsp hc)
    have hinput := Blocks.Copy.effect_bytes h.toStorage hc (size_firstBlock message)
      (by simpa only [size_firstBlock] using h.first)
    rw [← Blocks.Copy.effect_rsp hc] at hinput
    change (⟨(stackPtr u + BitVec.ofNat 64 104).toNat, (firstBlock message).size⟩ :
      MemoryRegion).HasBytes u.external (firstBlock message) at hinput
    rw [hus.stackAddress (by decide : 104 ≤ 280)] at hinput
    have hbuffer := Blocks.Copy.buffer_bytes hc h.buffer
    obtain ⟨hdi, hsi, hdx⟩ := Blocks.Copy.effect_arguments hc
    rw [← Blocks.Copy.effect_rsp hc] at hdi hsi
    have hp := hus.compressCallPre (src := 104) (dst := 0)
      (input := firstBlock message) (buffer := absorbedBuffer message)
      hsi (by change (.reg 7 : Operand 64).read u = stackPtr u + BitVec.ofNat 64 0
              simpa using hdi)
      (by change 64 * ((.reg 2 : Operand 64).read u).toNat = _
          rw [hdx, size_firstBlock]; rfl)
      (by rw [size_firstBlock]; decide) (by decide) (Or.inr (by decide))
      hinput (by simpa using hbuffer)
    obtain ⟨v, hv⟩ := Compression.first_run (update := update) hp hu hcu hOutside hc.rip
    have hvs := hus.of_agrees hv.agrees hv.rsp
    obtain ⟨m, t, hm, ht, hct, he⟩ := Blocks.Clear.run (update := update) hv.ready hv.code hvs hOutside hv.rip
    have hts := hvs.of_agrees he.agrees (Blocks.Clear.effect_rsp he)
    have hb : (⟨(stackPtr v).toNat, 16⟩ : MemoryRegion).HasBytes v.external
        ⟨(Standards.RFC.MD5.processBlocks (absorbedBuffer message)
          (Standards.RFC.MD5.wordsOfBytes (firstBlock message))).toBytes.toArray⟩ := by
      have hd : u.regValue .rdi = stackPtr u := hdi
      simpa only [Compress.outputRegion, registerRegion, hd, hv.rsp] using hv.output
    have hsu : Transition (update := update) boundary s u := ⟨⟨n, hn⟩, Blocks.Copy.transition_agrees hc⟩
    have huv : Transition (update := update) boundary u v := ⟨hv.advances, Compression.agrees hdi hv.agrees⟩
    have hvt : Transition (update := update) boundary v t := ⟨⟨m, hm⟩, Clear.agrees he⟩
    refine ⟨t, (hsu.trans huv).trans hvt, hts, ht, hct, he.rip, ?_, ?_, ?_, ?_⟩
    · rw [Blocks.Clear.effect_rsp he]
      simpa only [ite_eq_right hLong] using Blocks.Clear.effect_bytes hvs he
    · simpa only [paddedBuffer, ite_eq_right hLong] using Clear.buffer_bytes he hb
    · rw [(Blocks.Clear.effect_agrees he).read (n := 64) (r := 14) (by simp [Blocks.Clear.changes]),
        hv.agrees.read (n := 64) (r := 14) (by simp [FinalizeReset.CompressCall.changes]),
        (Blocks.Copy.effect_agrees hc).read (n := 64) (r := 14) (by simp [Blocks.Copy.changes])]
      exact h.blocks
    · rw [(Blocks.Clear.effect_agrees he).read (n := 64) (r := 15) (by simp [Blocks.Clear.changes]),
        hv.agrees.read (n := 64) (r := 15) (by simp [FinalizeReset.CompressCall.changes]),
        (Blocks.Copy.effect_agrees hc).read (n := 64) (r := 15) (by simp [Blocks.Copy.changes])]
      exact h.position

end Md5.Proofs.Buffered.Finalize.Streams.Slices
