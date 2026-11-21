import Md5.Proofs.Buffered.FinalizeReset.Pad.Short
import Md5.Proofs.Buffered.FinalizeReset.Copy
import Md5.Proofs.Buffered.FinalizeReset.CopyBridge
import Md5.Proofs.Buffered.FinalizeReset.Compression
import Md5.Proofs.Buffered.FinalizeReset.Clear.Properties

namespace Md5.Proofs.Buffered.FinalizeReset

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem pad_long {variant : Variant} [Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {s p : RamState} (hp : Pre boundary message s variant) (h : Prepare.Result boundary message s p variant)
    (hlong : 56 ≤ message.size % 64) :
    ∃ fuel t, Advances boundary fuel s t ∧ Padded message t variant ∧
      AgreesExcept (changes s) s t := by
  have hn : ¬ message.size % 64 < 56 := by omega
  obtain ⟨b, hbranch, hbready, hbcode, hbrip, hbframe⟩ := padding_branch (variant := variant) h.ready h.code
    hp.boundaryOutside h.rip (by omega : message.size % 64 < 64) h.remaining
  have hbsp : stackPtr b = stackPtr p := hbframe.read (n := 64) (r := 4) (by simp)
  have hbmem : b.external = p.external := hbframe.external (by simp [Component.Covers])
  have hbf : AgreesExcept (changes p) p b := hbframe.mono (by simp [changes])
  have hbs := agrees_storage h.storage hbf
  obtain ⟨ncopy, c, hcopy, hc⟩ := Copy.run .longTail hbready hbcode hbs hp.boundaryOutside
    (by simpa only [ite_eq_right hn, Copy.Kind.entry] using hbrip)
  have hcf := Copy.agrees_reset hc.agrees
  have hcs := agrees_storage hbs hcf
  have hcb : (⟨(stackPtr c + 0xe8).toNat, 16⟩ : MemoryRegion).HasBytes c.external
      ⟨(absorbedBuffer message).toBytes.toArray⟩ := by
    rw [hc.rsp]
    apply Copy.preserves_buffer hc.agrees
    simpa only [hbsp, h.rsp, hbmem] using h.copied
  have hci : (⟨(stackPtr c + 0x60).toNat, 64⟩ : MemoryRegion).HasBytes
      c.external (Finalize.firstBlock message) := by
    rw [hc.rsp]
    have hsrc : (⟨(stackPtr b + 8).toNat, (Finalize.firstBlock message).size⟩ : MemoryRegion).HasBytes
        b.external (Finalize.firstBlock message) := by
      simpa only [hbsp, h.rsp, hbmem, context, Prepare.firstBlock, Finalize.size_firstBlock]
        using h.padded
    have hh := Copy.effect_bytes hbs hc.effect (by rw [Finalize.size_firstBlock]; rfl) hsrc
    simpa only [Finalize.size_firstBlock] using hh
  have hcdi : c.regValue .rdi = stackPtr c + 0xe8 := by
    rw [hc.rsp]
    exact hc.rdi
  have hcsi : c.regValue .rsi = stackPtr c + 0x60 := by
    rw [hc.rsp]
    exact hc.rsi
  obtain ⟨d, hd⟩ := Compression.first (variant := variant)
    (Compression.pre hcs (Finalize.size_firstBlock message) hcdi hcsi hc.rdx hci hcb)
    hc.ready hc.code hp.boundaryOutside hc.rip
  have hdf := Compression.agrees hcdi hd.agrees
  have hds := agrees_storage hcs hdf
  obtain ⟨nclear, t, hclear, htready, htcode, hte⟩ :=
    Clear.run hd.ready hd.code hds hp.boundaryOutside hd.rip
  have htf := Clear.effect_agrees hte
  have htsp := agrees_rsp htf
  have hf := agrees_trans hp.toStorage h.agrees_reset hbf
  have hf := agrees_trans hp.toStorage hf hcf
  have hf := agrees_trans hp.toStorage hf hdf
  have hf := agrees_trans hp.toStorage hf htf
  have hposition : (Operand.reg 15 : Operand 64).read t = BitVec.ofNat 64 (message.size % 64) :=
    ((Clear.effect_frame hte).read (by simp)).trans
      ((hd.agrees.read (by simp [CompressCall.changes])).trans
        ((hc.agrees.read (by simp [Copy.changes])).trans
          ((hbframe.read (by simp)).trans h.position)))
  have hblocks : (Operand.reg 14 : Operand 64).read t = BitVec.ofNat 64 (message.size / 64) <<< 9 :=
    (hf.read (by simp [changes])).trans hp.bitBlocks
  have hdb : (⟨(stackPtr d + 0xe8).toNat, 16⟩ : MemoryRegion).HasBytes d.external
      ⟨(Standards.RFC.MD5.processBlocks (absorbedBuffer message)
        (Standards.RFC.MD5.wordsOfBytes (Finalize.firstBlock message))).toBytes.toArray⟩ := by
    rw [hd.rsp]
    simpa only [Compress.outputRegion, registerRegion, hcdi] using hd.output
  obtain ⟨nprepare, hprepare⟩ := h.advances
  obtain ⟨ncompress, hcompress⟩ := hd.advances
  refine ⟨nprepare + 2 + ncopy + ncompress + nclear, t,
    (((hprepare.trans hbranch).trans hcopy).trans hcompress).trans hclear,
    ⟨agrees_storage hds htf, htready, htcode, hte.rip, hposition, hblocks, ?_, ?_⟩, hf⟩
  · rw [htsp]
    simpa only [Finalize.paddedBuffer, ite_eq_right hn] using Clear.effect_buffer hte hdb
  · rw [htsp]
    simpa only [ite_eq_right hn] using Clear.effect_bytes hds hte

end Md5.Proofs.Buffered.FinalizeReset
