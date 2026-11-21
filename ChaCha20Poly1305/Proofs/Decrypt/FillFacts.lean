import ChaCha20Poly1305.Proofs.Decrypt.CopyFacts

namespace ChaCha20Poly1305.Proofs.Decrypt.Fill

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine Prelude
open ChaCha20Poly1305.Proofs.Decrypt.Copy (ptr ptr_nat ptr_ptr region)

structure Prefix (o m : Ram) (d : BitVec 64) (n i : Nat) : Prop where
  frame : RamWriteFrame o m [region d n]
  zero : ∀ j < i, memByte m (ptr d j) = 0

theorem start (o : Ram) (d : BitVec 64) (n : Nat) : Prefix o o d n 0 :=
  ⟨.refl .., by omega⟩

theorem guard {code o m d n i} {count p : BitVec 64} {size k : Nat}
    (h : Writable code o d n) (pre : Prefix o m d n i) (hl : i + size * count.toNat ≤ n)
    (hp : p.toNat + k ≤ 2^64) (hc : d.toNat + n ≤ p.toNat ∨ p.toNat + k ≤ d.toNat) :
    RepStosOk code m 0 (ptr d i) count size p k := by
  have := h.readable.low
  have hd := ptr_nat (a := d) (i := i) (by omega)
  have ds := (h.of_frame pre.frame).sub (a := ptr d i) (n := size * count.toNat)
    (by omega) (by omega)
  exact ⟨rfl, ds.readable.low, ds.readable.present, ds.tables,
    RangeApart.of_toNat (by omega) hp (by omega), ds.notCode⟩

theorem zero_replicate (w c : Nat) : (0#w).replicate c = 0#(w*c) := by
  apply BitVec.eq_of_getLsbD_eq
  simp [BitVec.getLsbD_replicate]

theorem advance {code o m d n i} (h : Writable code o d n) (pre : Prefix o m d n i)
    (w count : Nat) (hl : i + w*count/8 ≤ n) :
    Prefix o (memFill m (ptr d i) (0#w) count) d n (i + w*count/8) := by
  have := h.readable.low
  have hd := ptr_nat (a := d) (i := i) (by omega)
  let r := region (ptr d i) (w*count/8)
  have hw : RamWriteFrame m (memFill m (ptr d i) (0#w) count) [r] := by
    apply (RamWriteFrame.refl m [r]).memStore
    exact ⟨r, .head _, by simp only [r, region, InRegion]; omega⟩
  constructor
  · apply pre.frame.trans hw
    intro z hz
    simp only [List.mem_singleton] at hz
    subst z
    exact ⟨region d n, .head _, by simp only [r, region]; omega, by simp only [r, region]; omega⟩
  · intro j hj
    have hdj := ptr_nat (a := d) (i := j) (by omega)
    by_cases hij : j < i
    · have he := hw.outside (ptr d j) ⟨by omega, by
        simp only [List.mem_singleton, forall_eq, region, r]
        omega⟩
      rw [← pre.zero j hij]
      simp only [memByte, PhysicalMemory.read, he]
    · let k := j-i
      have hek : i+k = j := by dsimp [k]; omega
      have he := memStore_getElem?_self_of_le m (ptr d i) ((0#w).replicate count)
        (by omega) k (by omega)
      change (memFill m (ptr d i) (0#w) count)[ptr (ptr d i) k]? = _ at he
      rw [ptr_ptr, hek, zero_replicate] at he
      simp only [memByte, PhysicalMemory.read, he, storedByte, BitVec.toNat_zero,
        Nat.zero_shiftRight]
      rfl

end ChaCha20Poly1305.Proofs.Decrypt.Fill
