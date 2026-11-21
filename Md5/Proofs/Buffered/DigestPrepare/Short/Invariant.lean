import Md5.Proofs.Buffered.DigestPrepare.Geometry
import Md5.Proofs.Buffered.Update.Algebra

namespace Md5.Proofs.Buffered.DigestPrepare

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def shortChanges (s : RamState) (length : Nat) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11,
    .flags, .rip, .mem (stackPtr s + 176) length, .mem (pushAddr s) 8,
    .mem (stackPtr s + 239) 1]

theorem short_untouched [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    (h : Frame initial boundary s) {length : Nat} (hLength : length < 64)
    (ha : AgreesExcept (shortChanges s length) s t) (offset : Nat)
    (hl : 240 ≤ offset) (hh : offset < 264) :
    t.external[stackPtr s + BitVec.ofNat 64 offset]? =
      s.external[stackPtr s + BitVec.ofNat 64 offset]? := by
  have hlow := h.stackLow
  have hhigh : (stackPtr s).toNat + 264 < 2^32 := h.stackHigh
  apply ha.byte
  intro c hc hcov
  simp only [shortChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  all_goals try exact hcov.elim
  · obtain ⟨i, hi, he⟩ := hcov
    have hn := congrArg BitVec.toNat he
    change (stackPtr s + BitVec.ofNat 64 offset).toNat =
      (stackPtr s + BitVec.ofNat 64 176 + BitVec.ofNat 64 i).toNat at hn
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, h.address (by omega), h.address (by omega)] at hn
    omega
  · obtain ⟨i, hi, he⟩ := hcov
    have hn := congrArg BitVec.toNat he
    have hsn : (pushAddr s).toNat = (stackPtr s).toNat - 8 := by
      rw [pushAddr, BitVec.toNat_sub_of_le]
      · rfl
      · change 8 ≤ (stackPtr s).toNat
        omega
    rw [h.address (by omega), toNat_add_ofNat _ _ (by rw [hsn]; omega), hsn] at hn
    omega
  · obtain ⟨i, hi, he⟩ := hcov
    have hn := congrArg BitVec.toNat he
    change (stackPtr s + BitVec.ofNat 64 offset).toNat =
      (stackPtr s + BitVec.ofNat 64 239 + BitVec.ofNat 64 i).toNat at hn
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, h.address (by omega), h.address (by omega)] at hn
    omega

theorem short_absorbed [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    {input : ByteArray} (h : Frame initial boundary s) (hShort : input.size < 64)
    (hEmpty : Absorbed (Finalize.Kind.digest.context s) ByteArray.empty s)
    (ha : AgreesExcept (shortChanges s input.size) s t)
    (hTail : (⟨(stackPtr s).toNat + 176, input.size⟩ : MemoryRegion).HasBytes t.external input)
    (hPosition : (Operand.mem (stackPtr s + 239) : Operand 8).read t =
      BitVec.ofNat 8 input.size) : Absorbed (Finalize.Kind.digest.context s) input t := by
  have hcontext : (Finalize.Kind.digest.context s).toNat = (stackPtr s).toNat + 176 :=
    h.address (by decide)
  have heq : absorbedBuffer input = absorbedBuffer ByteArray.empty := by
    rw [absorbedBuffer, fullBytes_of_size_lt input hShort]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [heq]
    refine ⟨hEmpty.buffer.1, fun i ↦ ?_⟩
    apply Eq.trans _ (hEmpty.buffer.2 i)
    have hi : i.val < 16 := by
      simpa only [ByteArray.size, Vector.size_toArray] using i.isLt
    rw [hcontext]
    change t.external[BitVec.ofNat 64 ((stackPtr s).toNat + 176 + 64 + i.val)]? = _
    have he : BitVec.ofNat 64 ((stackPtr s).toNat + 176 + 64 + i.val) =
        stackPtr s + BitVec.ofNat 64 (240 + i.val) := by
      rw [show (stackPtr s).toNat + 176 + 64 + i.val = (stackPtr s).toNat + (240 + i.val)
        by omega, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [he]
    exact short_untouched h hShort ha _ (by omega) (by omega)
  · rw [tailBytes_of_size_lt input hShort, hcontext]
    exact hTail
  · simpa only [Finalize.Kind.context, Finalize.Kind.contextOffset, BitVec.add_assoc,
      BitVec.reduceAdd, Nat.mod_eq_of_lt hShort, BitVec.ofNat_eq_ofNat] using hPosition
  · have hb := hEmpty.blocks
    change (Operand.mem (stackPtr s + 176 + 80) : Operand 64).read s = 0 at hb
    change (Operand.mem (stackPtr s + 176 + 80) : Operand 64).read t = _
    rw [Nat.div_eq_of_lt hShort]
    refine Eq.trans ?_ hb
    apply memLoad_congr
    intro i hi
    apply congrArg (fun x : Option UInt8 ↦ x.getD 0)
    change t.external[stackPtr s + BitVec.ofNat 64 176 + BitVec.ofNat 64 80 + BitVec.ofNat 64 i]? =
      s.external[stackPtr s + BitVec.ofNat 64 176 + BitVec.ofNat 64 80 + BitVec.ofNat 64 i]?
    have he : stackPtr s + BitVec.ofNat 64 176 + BitVec.ofNat 64 80 + BitVec.ofNat 64 i =
        stackPtr s + BitVec.ofNat 64 (256 + i) := by
      simp only [BitVec.ofNat_add, BitVec.add_assoc]
      rw [← BitVec.add_assoc (176#64) (80#64)]
      simp only [BitVec.reduceAdd]
    rw [he]
    exact short_untouched h hShort ha (256 + i) (by omega) (by omega)

end Md5.Proofs.Buffered.DigestPrepare
