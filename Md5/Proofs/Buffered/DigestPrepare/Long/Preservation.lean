import Md5.Proofs.Buffered.DigestPrepare.Long.Contracts
import Md5.Proofs.Buffered.DigestPrepare.Short.Invariant
import Md5.Proofs.Buffered.DigestPrepare.Copy

namespace Md5.Proofs.Buffered.DigestPrepare.Long

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem State.preserve [Bindings] {initial s t : RamState} {input : ByteArray}
    {buffer : Standards.RFC.MD5.Buffer} (h : State initial input buffer s) {length : Nat}
    (hLength : length < 64) (ha : AgreesExcept (shortChanges s length) s t)
    (ht : Frame initial (returnBoundary initial) t) : State initial input buffer t := by
  have hsp : stackPtr t = stackPtr s := ha.read (n := 64) (r := 4) (by simp [shortChanges])
  refine ⟨ht, ?_, ?_, ?_, ?_⟩
  · rw [hsp]
    refine ⟨h.buffer.1, fun i ↦ ?_⟩
    apply Eq.trans _ (h.buffer.2 i)
    have hi : i.val < 16 := by
      simpa only [ByteArray.size, Vector.size_toArray] using i.isLt
    change t.external[BitVec.ofNat 64 ((stackPtr s).toNat + 240 + i.val)]? = _
    have he : BitVec.ofNat 64 ((stackPtr s).toNat + 240 + i.val) =
        stackPtr s + BitVec.ofNat 64 (240 + i.val) := by
      rw [Nat.add_assoc, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [he]
    exact short_untouched h.toFrame hLength ha _ (by omega) (by omega)
  · rw [hsp]
    refine Eq.trans ?_ h.blocks
    apply memLoad_congr
    intro i hi
    apply congrArg (fun x : Option UInt8 ↦ x.getD 0)
    change t.external[stackPtr s + BitVec.ofNat 64 256 + BitVec.ofNat 64 i]? =
      s.external[stackPtr s + BitVec.ofNat 64 256 + BitVec.ofNat 64 i]?
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact short_untouched h.toFrame hLength ha (256 + i) (by omega) (by omega)
  · exact (ha.read (n := 64) (r := 12) (by simp [shortChanges])).trans h.tailPointer
  · exact (ha.read (n := 64) (r := 15) (by simp [shortChanges])).trans h.tailSize

theorem position_after_memcpy [Bindings] {initial s t : RamState}
    {boundary : ReturnBoundary} {ret : BitVec 64}
    (h : Frame initial boundary s) (hr : MemcpySiteResult boundary ret s t)
    (hdi : rdi.read s = stackPtr s + 176)
    (hlen : (MemoryRoutines.rdx.read s).toNat < 64) :
    (Operand.mem (stackPtr t + 239) : Operand 8).read t =
      (Operand.mem (stackPtr s + 239) : Operand 8).read s := by
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
    change (stackPtr s + BitVec.ofNat 64 239).toNat =
      (stackPtr s + BitVec.ofNat 64 176 + BitVec.ofNat 64 j).toNat at hn
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, h.address (by omega), h.address (by omega)] at hn
    omega
  · obtain ⟨j, hj, he⟩ := hcov
    have hn := congrArg BitVec.toNat he
    have hl := h.stackLow
    have hh : (stackPtr s).toNat + 264 < 2^32 := h.stackHigh
    have hp : (pushAddr s).toNat = (stackPtr s).toNat - 8 := by
      rw [pushAddr, BitVec.toNat_sub_of_le]
      · rfl
      · change 8 ≤ (stackPtr s).toNat
        omega
    change (stackPtr s + BitVec.ofNat 64 239).toNat = _ at hn
    rw [h.address (by decide), toNat_add_ofNat _ _ (by rw [hp]; omega), hp] at hn
    omega

end Md5.Proofs.Buffered.DigestPrepare.Long
