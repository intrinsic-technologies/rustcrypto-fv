import Md5.Proofs.Buffered.DigestPrepare.Long.Compression.Pre

namespace Md5.Proofs.Buffered.DigestPrepare.Long

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [bindings : Bindings] {initial s t : RamState} {input : ByteArray}

theorem Prepared.compression_covers (h : Prepared initial input s)
    {c : Component} (hc : c ∈ FinalizeReset.CompressCall.changes s)
    {address : BitVec 64} (ha : c.Covers address) :
    ((stackPtr s).toNat - 320 ≤ address.toNat ∧ address.toNat < (stackPtr s).toNat) ∨
    ((stackPtr s).toNat + 240 ≤ address.toNat ∧
      address.toNat < (stackPtr s).toNat + 256) := by
  have hlo := h.stackLow
  have hhi : (stackPtr s).toNat + 264 < 2^32 := h.stackHigh
  simp only [FinalizeReset.CompressCall.changes, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  all_goals try exact ha.elim
  · obtain ⟨i, hi, rfl⟩ := ha
    rw [show s.regValue .rdi = stackPtr s + 240 from h.statePointerArg]
    have hn : (stackPtr s + 240 + BitVec.ofNat 64 i).toNat =
        (stackPtr s).toNat + 240 + i := by
      change (stackPtr s + BitVec.ofNat 64 240 + BitVec.ofNat 64 i).toNat = _
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, h.toFrame.address (by omega)]
      omega
    rw [hn]
    exact Or.inr ⟨by omega, by omega⟩
  · obtain ⟨i, hi, rfl⟩ := ha
    have hs : (stackPtr s - 320).toNat = (stackPtr s).toNat - 320 :=
      BitVec.toNat_sub_of_le hlo
    rw [toNat_add_ofNat _ _ (by rw [hs]; omega), hs]
    exact Or.inl ⟨by omega, by omega⟩

set_option maxRecDepth 4096 in
theorem Prepared.after_compression (hCall : Digest.ValidCall bindings initial input)
    (h : Prepared initial input s)
    (hr : FinalizeReset.CompressCall.Post (returnBoundary initial) 0x1000b3
      Standards.RFC.MD5.Buffer.initial (fullBytes input) s t) : Compressed initial input t := by
  have hframe : Frame initial (returnBoundary initial) t := by
    apply h.toFrame.preserve hCall.stackAvailable hr.agrees hr.ready hr.code
    · intro c hc hm
      simp only [FinalizeReset.CompressCall.changes, List.mem_cons, List.not_mem_nil,
        or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl
      all_goals simp_all [Component.isMem, digestPreparationChanges]
    · intro c hc address ha
      have hx := h.compression_covers hc ha
      change (stackPtr s).toNat - 320 ≤ address.toNat ∧
        address.toNat < (stackPtr s).toNat - 320 + 584
      have := h.stackLow
      omega
    · exact hr.rsp
    · exact hr.agrees.read (n := 64) (r := 3) (by simp [FinalizeReset.CompressCall.changes])
    · exact hr.agrees.read (n := 64) (r := 14) (by simp [FinalizeReset.CompressCall.changes])
  refine ⟨⟨hframe, ?_, ?_, ?_, ?_⟩, hr.rip⟩
  · rw [hr.rsp]
    exact h.outputRegion ▸ hr.output
  · rw [hr.rsp]
    apply Eq.trans _ h.blocks
    apply memLoad_congr
    intro i hi
    apply congrArg (fun x : Option UInt8 ↦ x.getD 0)
    apply hr.agrees.byte
    intro c hc ha
    have hx := h.compression_covers hc ha
    have hn : (stackPtr s + 256 + BitVec.ofNat 64 i).toNat =
        (stackPtr s).toNat + 256 + i := by
      change (stackPtr s + BitVec.ofNat 64 256 + BitVec.ofNat 64 i).toNat = _
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, h.toFrame.address (by omega)]
      omega
    rw [hn] at hx
    omega
  · exact (hr.agrees.read (n := 64) (r := 12)
      (by simp [FinalizeReset.CompressCall.changes])).trans h.tailPointer
  · exact (hr.agrees.read (n := 64) (r := 15)
      (by simp [FinalizeReset.CompressCall.changes])).trans h.tailSize

end Md5.Proofs.Buffered.DigestPrepare.Long
