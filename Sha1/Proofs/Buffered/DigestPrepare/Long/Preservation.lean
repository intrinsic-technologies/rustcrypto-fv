import Sha1.Proofs.Buffered.DigestPrepare.Long.Contracts
import Sha1.Proofs.Buffered.DigestPrepare.Short.Invariant
import Sha1.Proofs.Buffered.DigestPrepare.Copy

namespace Sha1.Proofs.Buffered.DigestPrepare.Long

open Sha1.Spec Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem hasBytes_extract {memory : Ram} {region : MemoryRegion} {bytes : ByteArray}
    (h : region.HasBytes memory bytes) (start stop : Nat) :
    (⟨region.start + start, (bytes.extract start stop).size⟩ : MemoryRegion).HasBytes
      memory (bytes.extract start stop) := by
  refine ⟨rfl, ?_⟩
  intro i
  have hi : start + i.val < bytes.size := ByteArray.getElem_extract_aux i.isLt
  simpa only [Nat.add_assoc, ByteArray.getElem_extract] using h.2 ⟨start + i.val, hi⟩

theorem State.preserve [Bindings] {initial s t : RamState} {input : ByteArray}
    {H : Vector (BitVec 32) 5} (h : State initial input H s)
    (hs : Stack.Valid initial Digest.minStackBytes) {length : Nat}
    (hLength : length < 64) (ha : AgreesExcept (shortChanges s length) s t)
    (ht : Frame initial (returnBoundary initial) t) : State initial input H t := by
  have hsp : stackPtr t = stackPtr s := ha.read (n := 64) (r := 4) (by simp [shortChanges])
  refine ⟨ht, ?_, ?_, ?_, ?_⟩
  · rw [hsp]
    refine ⟨h.hash.1, fun i ↦ ?_⟩
    apply Eq.trans _ (h.hash.2 i)
    have hi : i.val < 20 := by
      have := i.isLt
      simp only [Wrapper.Hash.Serialize.stateBytes_size] at this
      exact this
    change t.external[BitVec.ofNat 64 ((stackPtr s).toNat + 0x100 + i.val)]? = _
    have he : BitVec.ofNat 64 ((stackPtr s).toNat + 0x100 + i.val) =
        stackPtr s + BitVec.ofNat 64 (0x100 + i.val) := by
      rw [Nat.add_assoc, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [he]
    exact short_untouched h.toFrame hs hLength ha _ (by omega) (by omega)
  · rw [hsp]
    refine Eq.trans ?_ h.blocks
    apply memLoad_congr
    intro i hi
    apply congrArg (fun x : Option UInt8 ↦ x.getD 0)
    change t.external[stackPtr s + BitVec.ofNat 64 0xf8 + BitVec.ofNat 64 i]? =
      s.external[stackPtr s + BitVec.ofNat 64 0xf8 + BitVec.ofNat 64 i]?
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact short_untouched h.toFrame hs hLength ha (0xf8 + i) (by omega) (by omega)
  · exact (ha.read (n := 64) (r := 12) (by simp [shortChanges])).trans h.tailPointer
  · exact (ha.read (n := 64) (r := 15) (by simp [shortChanges])).trans h.tailSize

theorem position_after_memcpy [bindings : Bindings] {initial s t : RamState} {input : ByteArray}
    {ret : BitVec 64} (hCall : Digest.ValidCall bindings initial input)
    (h : Frame initial (returnBoundary initial) s)
    (hr : MemcpySiteResult (returnBoundary initial) ret s t)
    (hdi : rdi.read s = stackPtr s + 184)
    (hlen : (MemoryRoutines.rdx.read s).toNat < 64) :
    (Operand.mem (stackPtr t + 0xf7) : Operand 8).read t =
      (Operand.mem (stackPtr s + 0xf7) : Operand 8).read s := by
  have hs := hCall.stackAvailable
  have hst := h.storage hCall
  rw [hr.rsp]
  apply memLoad_congr
  intro i hi
  have hi0 : i = 0 := by omega
  subst i
  apply congrArg (fun x : Option UInt8 ↦ x.getD 0)
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero]
  apply hr.agrees.byte
  intro c hc hcov
  simp only [callSiteChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hcov.elim
  · obtain ⟨j, hj, he⟩ := hcov
    rw [hdi] at he
    have hn := congrArg BitVec.toNat he
    change (stackPtr s + BitVec.ofNat 64 0xf7).toNat =
      (stackPtr s + BitVec.ofNat 64 184 + BitVec.ofNat 64 j).toNat at hn
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, h.address hs (by omega),
      h.address hs (by omega)] at hn
    omega
  · obtain ⟨j, hj, he⟩ := hcov
    have hn := congrArg BitVec.toNat he
    have hl := hst.stackLow
    have hfb : Finalize.Kind.frameBytes = 344 := rfl
    have hh : (stackPtr s).toNat + 0x118 < 2^32 := hst.stackHigh
    have hp : (pushAddr s).toNat = (stackPtr s).toNat - 8 := by
      rw [pushAddr, BitVec.toNat_sub_of_le]
      · rfl
      · change 8 ≤ (stackPtr s).toNat
        omega
    change (stackPtr s + BitVec.ofNat 64 0xf7).toNat = _ at hn
    rw [h.address hs (by decide), toNat_add_ofNat _ _ (by rw [hp]; omega), hp] at hn
    omega

end Sha1.Proofs.Buffered.DigestPrepare.Long
