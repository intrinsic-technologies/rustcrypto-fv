import Sha1.Proofs.Buffered.DigestPrepare.Geometry

namespace Sha1.Proofs.Buffered.DigestPrepare

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def shortChanges (s : RamState) (length : Nat) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11,
    .flags, .rip, .mem (stackPtr s + 184) length, .mem (pushAddr s) 8,
    .mem (stackPtr s + 0xf7) 1]

theorem fullBytes_of_size_lt (input : ByteArray) (h : input.size < 64) :
    fullBytes input = fullBytes ByteArray.empty := by
  simp only [fullBytes, Sha1.Proofs.Wrapper.Absorb.fullBlocks, Nat.div_eq_of_lt h,
    ByteArray.size_empty, Nat.zero_div, Nat.mul_zero, ByteArray.extract_same]

theorem absorbedStateBytes_of_size_lt (input : ByteArray) (h : input.size < 64) :
    absorbedStateBytes input = absorbedStateBytes ByteArray.empty := by
  simp only [absorbedStateBytes, absorbedHash, fullBytes_of_size_lt input h]

variable [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}

theorem short_untouched (h : Frame initial boundary s)
    (hs : Stack.Valid initial Digest.minStackBytes) {length : Nat} (hLength : length < 64)
    (ha : AgreesExcept (shortChanges s length) s t) (offset : Nat)
    (hl : 0xf8 ≤ offset) (hh : offset < 0x118) :
    t.external[stackPtr s + BitVec.ofNat 64 offset]? =
      s.external[stackPtr s + BitVec.ofNat 64 offset]? := by
  have hb := stack_bounds hs
  have hn := h.stackNat hs
  apply ha.byte
  intro c hc hcov
  simp only [shortChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  all_goals try exact hcov.elim
  · obtain ⟨i, hi, he⟩ := hcov
    have hn' := congrArg BitVec.toNat he
    change (stackPtr s + BitVec.ofNat 64 offset).toNat =
      (stackPtr s + BitVec.ofNat 64 184 + BitVec.ofNat 64 i).toNat at hn'
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, h.address hs (by omega),
      h.address hs (by omega)] at hn'
    omega
  · obtain ⟨i, hi, he⟩ := hcov
    have hn' := congrArg BitVec.toNat he
    have hsn : (pushAddr s).toNat = (stackPtr s).toNat - 8 := by
      rw [pushAddr, BitVec.toNat_sub_of_le]
      · rfl
      · change 8 ≤ (stackPtr s).toNat
        omega
    rw [h.address hs (by omega), toNat_add_ofNat _ _ (by rw [hsn]; omega), hsn] at hn'
    omega
  · obtain ⟨i, hi, he⟩ := hcov
    have hn' := congrArg BitVec.toNat he
    change (stackPtr s + BitVec.ofNat 64 offset).toNat =
      (stackPtr s + BitVec.ofNat 64 0xf7 + BitVec.ofNat 64 i).toNat at hn'
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, h.address hs (by omega),
      h.address hs (by omega)] at hn'
    omega

theorem short_absorbed (h : Frame initial boundary s)
    (hs : Stack.Valid initial Digest.minStackBytes) {input : ByteArray}
    (hShort : input.size < 64)
    (hEmpty : Absorbed (stackPtr s + 0xb8) ByteArray.empty s)
    (ha : AgreesExcept (shortChanges s input.size) s t)
    (hTail : (⟨(stackPtr s).toNat + 184, input.size⟩ : MemoryRegion).HasBytes t.external input)
    (hPosition : (Operand.mem (stackPtr s + 0xf7) : Operand 8).read t =
      BitVec.ofNat 8 input.size) : Absorbed (stackPtr s + 0xb8) input t := by
  have hbase : (stackPtr s + 0xb8).toNat = (stackPtr s).toNat + 184 :=
    h.address hs (offset := 184) (by decide)
  have hstate : (stackPtr s + 0xb8 + 72).toNat = (stackPtr s).toNat + 0x100 := by
    rw [BitVec.add_assoc]
    exact h.address hs (offset := 0x100) (by decide)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [absorbedStateBytes_of_size_lt input hShort]
    refine ⟨hEmpty.state.1, fun i ↦ ?_⟩
    apply Eq.trans _ (hEmpty.state.2 i)
    have hi : i.val < 20 := by
      have := absorbedStateBytes_size ByteArray.empty
      omega
    rw [hstate]
    have he : BitVec.ofNat 64 ((stackPtr s).toNat + 0x100 + i.val) =
        stackPtr s + BitVec.ofNat 64 (0x100 + i.val) := by
      rw [show (stackPtr s).toNat + 0x100 + i.val = (stackPtr s).toNat + (0x100 + i.val)
        by omega, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [he]
    exact short_untouched h hs hShort ha _ (by omega) (by omega)
  · rw [show tailBytes input = input from
      Sha1.Proofs.Wrapper.Absorb.remainderBytes_short input hShort, hbase]
    exact hTail
  · rw [size_tailBytes, Nat.mod_eq_of_lt hShort]
    have hp : (stackPtr s + 0xb8 + 63 : BitVec 64) = stackPtr s + 0xf7 := by
      rw [BitVec.add_assoc]
      rfl
    rw [hp]
    exact hPosition
  · have hb := hEmpty.blocks
    change (Operand.mem (stackPtr s + 0xb8 + 64) : Operand 64).read s = _ at hb
    change (Operand.mem (stackPtr s + 0xb8 + 64) : Operand 64).read t = _
    rw [Nat.div_eq_of_lt hShort]
    refine Eq.trans ?_ hb
    apply memLoad_congr
    intro i hi
    apply congrArg (fun x : Option UInt8 ↦ x.getD 0)
    have he : stackPtr s + 0xb8 + 64 + BitVec.ofNat 64 i =
        stackPtr s + BitVec.ofNat 64 (0xf8 + i) := by
      rw [BitVec.ofNat_add]
      simp only [BitVec.add_assoc]
      congr 1
      rw [← BitVec.add_assoc]
      rfl
    change t.external[stackPtr s + 0xb8 + 64 + BitVec.ofNat 64 i]? =
      s.external[stackPtr s + 0xb8 + 64 + BitVec.ofNat 64 i]?
    rw [he]
    exact short_untouched h hs hShort ha (0xf8 + i) (by omega) (by omega)

end Sha1.Proofs.Buffered.DigestPrepare
