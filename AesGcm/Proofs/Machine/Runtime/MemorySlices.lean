import AesGcm.Proofs.Machine.Runtime.Root.Memory
namespace AesGcm.Proofs.Machine.Runtime
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.Refine

theorem hasBytes_extract {mem : Ram} {base : BitVec 64} {bytes : ByteArray}
    (h : (span base bytes.size).HasBytes mem bytes) (lo hi : Nat)
    (hlo : lo ≤ hi) (hhi : hi ≤ bytes.size)
    (hbound : base.toNat + lo < 2 ^ 64) :
    (span (base + BitVec.ofNat 64 lo) (hi - lo)).HasBytes mem (bytes.extract lo hi) := by
  have hstart : (base + BitVec.ofNat 64 lo).toNat = base.toNat + lo := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show lo < 2 ^ 64 by omega), Nat.mod_eq_of_lt hbound]
  refine ⟨by simp [MemoryRegion.HasLength, span, ByteArray.size_extract, Nat.min_eq_left hhi], ?_⟩
  intro i
  have hi' : i.val < hi - lo := by
    simpa only [ByteArray.size_extract, Nat.min_eq_left hhi] using i.isLt
  have hv := h.2 ⟨lo + i.val, by omega⟩
  change mem[BitVec.ofNat 64 ((base + BitVec.ofNat 64 lo).toNat + i.val)]? =
    some (bytes.extract lo hi)[i.val]
  rw [hstart, Nat.add_assoc, ByteArray.getElem_extract]
  exact hv

theorem hasBytes_append {mem : Ram} {base : BitVec 64} {front tail : ByteArray}
    (hf : (span base front.size).HasBytes mem front)
    (ht : (span (base + BitVec.ofNat 64 front.size) tail.size).HasBytes mem tail)
    (hbound : base.toNat + front.size < 2 ^ 64) :
    (span base (front.size + tail.size)).HasBytes mem (front ++ tail) := by
  have hstart : (base + BitVec.ofNat 64 front.size).toNat = base.toNat + front.size := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show front.size < 2 ^ 64 by omega), Nat.mod_eq_of_lt hbound]
  refine ⟨by simp [MemoryRegion.HasLength, span], ?_⟩
  intro i
  by_cases hi : i.val < front.size
  · rw [ByteArray.getElem_append_left hi]
    exact hf.2 ⟨i.val, hi⟩
  · have hit : i.val - front.size < tail.size := by
      have := i.isLt
      simp only [ByteArray.size_append] at this
      omega
    have hv := ht.2 ⟨i.val - front.size, hit⟩
    change mem[BitVec.ofNat 64 ((base + BitVec.ofNat 64 front.size).toNat + (i.val - front.size))]? = _ at hv
    rw [hstart, Nat.add_assoc, Nat.add_sub_of_le (by omega : front.size ≤ i.val)] at hv
    rw [ByteArray.getElem_append_right (by omega)]
    exact hv

theorem hasBytes_of_copy {before after : Ram} {source destination : BitVec 64} {bytes : ByteArray}
    (hbytes : (span source bytes.size).HasBytes before bytes)
    (hcopy : ∀ i < bytes.size,
      after[destination + BitVec.ofNat 64 i]? = before[source + BitVec.ofNat 64 i]?) :
    (span destination bytes.size).HasBytes after bytes := by
  refine ⟨rfl, fun i ↦ ?_⟩
  have hb := hbytes.2 i
  change before[BitVec.ofNat 64 (source.toNat + i.val)]? = some bytes[i.val] at hb
  change after[BitVec.ofNat 64 (destination.toNat + i.val)]? = some bytes[i.val]
  simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hb ⊢
  rw [hcopy i.val i.isLt]
  exact hb

theorem memLoad_eq_of_disjoint {before after : Ram} {regions : List MemoryRegion}
    (hframe : RamWriteFrame before after regions) {a : BitVec 64} {k : Nat}
    (hbound : a.toNat + k / 8 ≤ 2^64)
    (hapart : ∀ r ∈ regions, (span a (k / 8)).Disjoint r) :
    memLoad after a k = memLoad before a k := by
  apply memLoad_congr
  intro i hi
  have ha : (a + BitVec.ofNat 64 i).toNat = a.toNat + i := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := i) (by omega), Nat.mod_eq_of_lt (by omega)]
  simp only [memByte, PhysicalMemory.read]
  rw [hframe.outside _ ⟨by rw [ha]; omega, ?_⟩]
  intro r hr
  have hn := hapart r hr (a.toNat + i)
    (show (span a (k / 8)).Contains (a.toNat + i) from ⟨by simp [span], by simp [span]; omega⟩)
  rw [ha]
  simp only [MemoryRegion.Contains] at hn
  omega

end AesGcm.Proofs.Machine.Runtime
