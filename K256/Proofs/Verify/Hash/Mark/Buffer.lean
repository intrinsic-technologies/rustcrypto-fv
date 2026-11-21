import K256.Proofs.Verify.Hash.Padding.Finalize
import K256.Proofs.Verify.Hash.Mark.Copy
import X86Proofs.Program.ReadWrite.Bytes

namespace K256.Proofs.Verify.Hash.Mark

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.Lift K256.Proofs.Refine

private theorem byte_before (msg : ByteArray) (i : Nat) (hi : i < msg.size % 64) :
    (paddedBuffer msg)[i]! = (remainderBytes msg)[i]! := by
  have r : i < (remainderBytes msg).size := by rwa [remainderBytes_size]
  rw [getElem!_pos _ _ (by rw [paddedBuffer_size]; omega), getElem!_pos (remainderBytes msg) i r]
  unfold paddedBuffer
  rw [ByteArray.getElem_append_left (by rw [ByteArray.size_append]; omega),
    ByteArray.getElem_append_left r]

private theorem byte_marker (msg : ByteArray) : (paddedBuffer msg)[msg.size % 64]! = 128 := by
  have s := remainderBytes_size msg
  have b := Nat.mod_lt msg.size (by decide : 0 < 64)
  rw [getElem!_pos _ _ (by rw [paddedBuffer_size]; omega)]
  unfold paddedBuffer
  rw [ByteArray.getElem_append_left (by rw [ByteArray.size_append, s]; change _ < _ + 1; omega),
    ByteArray.getElem_append_right (by omega)]
  simp [s]
  rfl

private theorem byte_after (msg : ByteArray) (i : Nat) (hm : msg.size % 64 < i) (hi : i < 64) :
    (paddedBuffer msg)[i]! = 0 := by
  have s := remainderBytes_size msg
  rw [getElem!_pos _ _ (by rwa [paddedBuffer_size])]
  unfold paddedBuffer
  rw [ByteArray.getElem_append_right (by rw [ByteArray.size_append, s]; change _ + 1 ≤ _; omega)]
  exact Array.getElem_replicate _

set_option maxHeartbeats 400000 in
theorem buffer_after_fill {m out : Ram} {sp : BitVec 64} (msg : ByteArray)
    (low : sp.toNat + 352 ≤ 2^32)
    (tail : (⟨(sp+248).toNat, msg.size % 64⟩ : MemoryRegion).HasBytes m (remainderBytes msg))
    (frame : RamWriteFrame (pushed m sp (msg.size % 64)) out
      [⟨(sp + 9 + BitVec.ofNat 64 (msg.size % 64)).toNat, 63 - msg.size % 64⟩])
    (readable : Readable out (sp + 8) 64)
    (zero : ∀ i < 63 - msg.size % 64, memByte out
      (sp + 9 + BitVec.ofNat 64 (msg.size % 64) + BitVec.ofNat 64 i) = 0) :
    (⟨(sp+8).toNat, 64⟩ : MemoryRegion).HasBytes out (paddedBuffer msg) := by
  let n := msg.size % 64
  let base := sp + 8
  let dst := sp + 9 + BitVec.ofNat 64 n
  have b : n < 64 := Nat.mod_lt _ (by decide)
  have addr (k : Nat) (hk : k ≤ 352) :
      (sp + BitVec.ofNat 64 k).toNat = sp.toNat + k := toNat_add_ofNat _ _ (by omega)
  have baseNat : base.toNat = sp.toNat + 8 := addr 8 (by decide)
  have nine : (sp + 9).toNat = sp.toNat + 9 := addr 9 (by decide)
  have dstNat : dst.toNat = sp.toNat + 9 + n := by
    change (sp + 9 + BitVec.ofNat 64 n).toNat = _
    rw [toNat_add_ofNat _ _ (by omega), nine]
  have copiedPrefix : Bytes (copied m sp) base n (fun i => (paddedBuffer msg)[i]!) := by
    intro i hi
    change _ = some ((paddedBuffer msg)[i]!)
    rw [Sec1.Wrapper.Copy.memCopy_getElem?_self _ _ _ _ (by decide) _ (by omega),
      byte_before msg i hi, getElem!_pos (remainderBytes msg) i (by rw [remainderBytes_size]; exact hi)]
    have h := tail.2 ⟨i, by rw [remainderBytes_size]; exact hi⟩
    simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h
    change some ((m[sp + 248 + BitVec.ofNat 64 i]?).getD 0) = _
    rw [h]
    rfl
  have marker := copiedPrefix.append_store (128 : BitVec 8) (by decide) (by omega) (by
    intro i hi
    have : i = 0 := by omega
    subst i
    simp only [n, Nat.add_zero, byte_marker]
    rfl)
  have markedPrefix : Bytes (pushed m sp n) base (n+1) (fun i => (paddedBuffer msg)[i]!) :=
    marker.store_disjoint _ _ (RangeApart.of_offsets (addr_sub sp 8) rfl (by
      change 8 ≤ 16 ∧ n + 1 ≤ 18446744073709551600
      omega))
  refine ⟨paddedBuffer_size msg, fun i => ?_⟩
  have hi : i.val < 64 := by simpa only [paddedBuffer_size] using i.isLt
  change out[BitVec.ofNat 64 (base.toNat + i.val)]? = _
  simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [← getElem!_pos (paddedBuffer msg) i.val i.isLt]
  by_cases hp : i.val < n + 1
  · apply Eq.trans (frame.outside _ ?_) (markedPrefix _ hp)
    have pos := toNat_add_ofNat base i.val (by omega)
    refine ⟨by omega, fun r hr => Or.inl ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    change _ ≤ dst.toNat
    omega
  · have pos : base + BitVec.ofNat 64 i.val = dst + BitVec.ofNat 64 (i.val - (n+1)) := by
      change sp + 8 + BitVec.ofNat 64 i.val = sp + 9 + BitVec.ofNat 64 n + BitVec.ofNat 64 _
      have eq : 8 + i.val = 9 + n + (i.val - (n+1)) := by omega
      calc
        _ = sp + BitVec.ofNat 64 (8 + i.val) := by simp only [BitVec.ofNat_add, BitVec.add_assoc]; rfl
        _ = sp + BitVec.ofNat 64 (9 + n + (i.val - (n+1))) := congrArg (fun k => sp + BitVec.ofNat 64 k) eq
        _ = _ := by simp only [BitVec.ofNat_add, BitVec.add_assoc]; rfl
    rw [byte_after msg i.val (by change n < _; omega) hi]
    have h := (Bytes.of_isSome readable.present) i.val hi
    change out[base + BitVec.ofNat 64 i.val]? = some (memByte out (base + BitVec.ofNat 64 i.val)) at h
    rw [pos] at h ⊢
    have hz := zero (i.val - (n+1)) (by change _ < 63 - n; omega)
    exact h.trans (congrArg some hz)

end K256.Proofs.Verify.Hash.Mark
