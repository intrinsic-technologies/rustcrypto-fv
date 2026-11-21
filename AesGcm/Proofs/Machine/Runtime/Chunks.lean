import AesGcm.Proofs.Copied.X86Proofs.Lift.Rep
import X86Proofs.Program.ReadWrite.Store

namespace AesGcm.Proofs.Machine.Runtime

open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.Lift

theorem memCopy_getElem?_self (m : Ram) (dst src : BitVec 64) (len : Nat)
    (hlen : len ≤ 2 ^ 64) (i : Nat) (hi : i < len) :
    (memCopy m dst src len)[dst + BitVec.ofNat 64 i]? =
      some (memByte m (src + BitVec.ofNat 64 i)) := by
  unfold memCopy
  rw [memStore_getElem?_self_of_le m dst _ (by omega) i (by omega),
    storedByte_memLoad m src i (by omega)]

theorem memCopy_getElem?_of_ne (m : Ram) (dst src x : BitVec 64) (len : Nat)
    (hx : ∀ i < len, dst + BitVec.ofNat 64 i ≠ x) :
    (memCopy m dst src len)[x]? = m[x]? := by
  exact memStore_getElem?_of_ne m dst _ x (by
    intro i hi
    exact hx i (by omega))

theorem memCopy_getElem?_source (m : Ram) (dst src : BitVec 64) (len : Nat)
    (hap : RangeApart src len dst len) (i : Nat) (hi : i < len) :
    (memCopy m dst src len)[src + BitVec.ofNat 64 i]? = m[src + BitVec.ofNat 64 i]? := by
  apply memCopy_getElem?_of_ne
  intro j hj he
  exact hap i hi j hj he.symm

theorem memCopy_append (m : Ram) (dst src : BitVec 64) (h q : Nat)
    (hlen : h + q ≤ 2 ^ 64) (hap : RangeApart src (h + q) dst (h + q)) :
    memCopy (memCopy m dst src h) (dst + BitVec.ofNat 64 h)
      (src + BitVec.ofNat 64 h) q = memCopy m dst src (h + q) := by
  have hsrc (j : Nat) (hj : j < q) :
      memByte (memCopy m dst src h) (src + BitVec.ofNat 64 (h + j)) =
        memByte m (src + BitVec.ofNat 64 (h + j)) := by
    unfold memByte
    simp only [PhysicalMemory.read]
    rw [memCopy_getElem?_of_ne]
    intro i hi he
    exact hap (h + j) (by omega) i (by omega) he.symm
  apply Std.ExtHashMap.ext_getElem?
  intro x
  by_cases hq : ∃ j < q, dst + BitVec.ofNat 64 h + BitVec.ofNat 64 j = x
  · obtain ⟨j, hj, rfl⟩ := hq
    rw [memCopy_getElem?_self _ _ _ q (by omega) j hj]
    simp only [BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [hsrc j hj, memCopy_getElem?_self _ _ _ (h + q) hlen (h + j) (by omega)]
  · rw [memCopy_getElem?_of_ne _ _ _ x q (by
      intro j hj he
      exact hq ⟨j, hj, he⟩)]
    by_cases hh : ∃ i < h, dst + BitVec.ofNat 64 i = x
    · obtain ⟨i, hi, rfl⟩ := hh
      rw [memCopy_getElem?_self _ _ _ h (by omega) i hi,
        memCopy_getElem?_self _ _ _ (h + q) hlen i (by omega)]
    · rw [memCopy_getElem?_of_ne _ _ _ x h (by
        intro i hi he
        exact hh ⟨i, hi, he⟩)]
      symm
      apply memCopy_getElem?_of_ne
      intro i hi he
      by_cases ih : i < h
      · exact hh ⟨i, ih, he⟩
      · apply hq
        refine ⟨i - h, by omega, ?_⟩
        simpa only [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_of_le (by omega : h ≤ i)] using he

theorem memCopy_three (m : Ram) (dst src : BitVec 64) (h q t : Nat)
    (hlen : h + q + t ≤ 2 ^ 64)
    (hap : RangeApart src (h + q + t) dst (h + q + t)) :
    memCopy (memCopy (memCopy m dst src h)
        (dst + BitVec.ofNat 64 h) (src + BitVec.ofNat 64 h) q)
      (dst + BitVec.ofNat 64 (h + q)) (src + BitVec.ofNat 64 (h + q)) t =
      memCopy m dst src (h + q + t) := by
  rw [memCopy_append m dst src h q (by omega) (by
    intro i hi j hj
    exact hap i (by omega) j (by omega)), memCopy_append m dst src (h + q) t hlen hap]

end AesGcm.Proofs.Machine.Runtime
