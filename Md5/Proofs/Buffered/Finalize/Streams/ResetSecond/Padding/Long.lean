import Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Padding.Branch
import Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Padding.Compression
import Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Padding.Clear
import Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Copy

namespace Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Padding

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Block

theorem long [Bindings] {variant : Variant} {boundary : ReturnBoundary} {message : ByteArray} {s : RamState}
    (hOutside : ¬ InProgram boundary.rip) (h : Prepared message s variant)
    (hlong : ¬ message.size % 64 < 56) :
    ∃ t, Transition boundary s t variant ∧ Padded message t variant := by
  obtain ⟨b, hbranch, hbready, hbcode, hbrip, hbframe⟩ := branch h.ready h.code
    hOutside h.rip (by omega : message.size % 64 < 64) h.remaining
  have hbsp : stackPtr b = stackPtr s := hbframe.read (n := 64) (r := 4) (by simp)
  have hbmem : b.external = s.external := hbframe.external (by simp [Component.Covers])
  have hbs := h.toStorage.of_agrees hbframe hbsp
  obtain ⟨ncopy, c, hcopy, hcready, hccode, hc⟩ := Copy.run (kind := .longTail) (variant := variant)
    hOutside hbready hbcode ⟨hbs, by cases variant <;> simpa only [Copy.Kind.entry, longEntry, ite_eq_right hlong] using hbrip⟩
  have hcsp := Copy.effect_rsp hc
  have hcs := hbs.of_agrees hc.agrees hcsp
  have haddrBlock : (stackPtr c + BitVec.ofNat 64 variant.blockOffset).toNat = (stackPtr c).toNat + variant.blockOffset :=
    hcs.stackAddress (by cases variant <;> decide : variant.blockOffset ≤ variant.toKind.stackBytes)
  have haddrResult : (stackPtr c + BitVec.ofNat 64 variant.resultOffset).toNat = (stackPtr c).toNat + variant.resultOffset :=
    hcs.stackAddress (by cases variant <;> decide : variant.resultOffset ≤ variant.toKind.stackBytes)
  have hcb := Copy.buffer_bytes hc (by simpa only [hbsp, hbmem] using h.buffer)
  have hcfirst : Bytes c.external (stackPtr c + BitVec.ofNat 64 variant.blockOffset) 64
      (fun i ↦ (firstBlock message)[i]!) := by
    rw [hcsp]
    intro i hi
    exact (Copy.effect_copy hbs hc i hi).trans (by
      simpa only [hbsp, hbmem] using h.first i hi)
  have hcinput : (⟨(stackPtr c).toNat + variant.blockOffset, (firstBlock message).size⟩ : MemoryRegion).HasBytes
      c.external (firstBlock message) := by
    have hb := hasBytes_of_bytes (bytes := firstBlock message)
      (by simpa only [size_firstBlock] using hcfirst)
    rw [haddrBlock] at hb
    exact hb
  obtain ⟨hdi, hsi, hdx⟩ := Copy.effect_arguments hc
  rw [← hcsp] at hdi hsi
  change c.regValue .rdi = stackPtr c + BitVec.ofNat 64 variant.resultOffset at hdi
  change c.regValue .rsi = stackPtr c + BitVec.ofNat 64 variant.blockOffset at hsi
  change c.regValue .rdx = 1 at hdx
  have hp := hcs.compressCallPre (src := variant.blockOffset) (dst := variant.resultOffset)
    hsi hdi (by rw [hdx, size_firstBlock]; rfl)
    (by rw [size_firstBlock]; cases variant <;> decide) (by cases variant <;> decide)
    (Or.inr (by cases variant <;> decide)) hcinput hcb
  obtain ⟨d, hd⟩ := compress (variant := variant) hp hcready hccode hOutside (by cases variant <;> exact hc.rip)
  have hds := hcs.of_agrees hd.agrees hd.rsp
  obtain ⟨t, hdt, htready, htcode, htrip, htframe, htbytes⟩ :=
    Clear.run hOutside hd.ready hd.code hds (by cases variant <;> exact hd.rip)
  have hsb : Transition boundary s b variant := ⟨⟨2, hbranch⟩,
    hbframe.mono (by simp [Kind.changes])⟩
  have hbc : Transition boundary b c variant := ⟨⟨ncopy, hcopy⟩, Copy.transition_agrees hc⟩
  have hcd : Transition boundary c d variant := ⟨hd.advances, Compression.agrees hdi hd.agrees⟩
  refine ⟨t, ((hsb.trans hbc).trans hcd).trans hdt,
    hds.of_agrees htframe hdt.rsp, htready, htcode, htrip, ?_, ?_, ?_, ?_⟩
  · simpa only [ite_eq_right hlong] using htbytes
  · have hdb : (⟨(stackPtr d).toNat + variant.resultOffset, 16⟩ : MemoryRegion).HasBytes d.external
        ⟨(paddedBuffer message).toBytes.toArray⟩ := by
      rw [hd.rsp]
      have hb := hd.output
      simp only [Compress.outputRegion, registerRegion, hdi,
        haddrResult] at hb
      simpa only [paddedBuffer, ite_eq_right hlong] using hb
    rw [hdt.rsp]
    refine ⟨hdb.1, ?_⟩
    intro i
    have hi : i.val < 16 := by simpa only [ByteArray.size, Vector.size_toArray] using i.isLt
    have hb := hdb.2 i
    change t.external[BitVec.ofNat 64 ((stackPtr d).toNat + variant.resultOffset + i.val)]? = _
    change d.external[BitVec.ofNat 64 ((stackPtr d).toNat + variant.resultOffset + i.val)]? = _ at hb
    simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hb ⊢
    refine Eq.trans (htframe.byte ?_) hb
    intro c hc ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ha.elim
    · obtain ⟨j, hj, he⟩ := ha
      exact (show OffsetsApart variant.tailOffset 56 (BitVec.ofNat 64 variant.resultOffset) 16 by unfold OffsetsApart; cases variant <;> decide).ne
        (stackPtr d) hj hi (by cases variant <;> decide) he.symm
  · exact (htframe.read (by simp)).trans
      ((hd.agrees.read (by simp [FinalizeReset.CompressCall.changes])).trans
        (((Copy.effect_agrees hc).read (by simp [Copy.changes])).trans
          ((hbframe.read (by simp)).trans h.blocks)))
  · exact (htframe.read (by simp)).trans
      ((hd.agrees.read (by simp [FinalizeReset.CompressCall.changes])).trans
        (((Copy.effect_agrees hc).read (by simp [Copy.changes])).trans
          ((hbframe.read (by simp)).trans h.position)))

end Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Padding
