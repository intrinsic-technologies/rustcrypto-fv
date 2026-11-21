import ChaCha20Poly1305.Proofs.Common.Refine.Lemma.Store
import ChaCha20Poly1305.Proofs.Common.Lift.Rep

namespace ChaCha20Poly1305.Proofs.Decrypt.Copy

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine Prelude

def ptr (a : BitVec 64) (i : Nat) := a + BitVec.ofNat 64 i

theorem ptr_nat {a : BitVec 64} {i : Nat} (h : a.toNat + i < 2^64) :
    (ptr a i).toNat = a.toNat + i := by
  simp only [ptr, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := i) (by omega), Nat.mod_eq_of_lt h]

theorem ptr_ptr (a : BitVec 64) (i j : Nat) : ptr (ptr a i) j = ptr a (i + j) := by
  simp only [ptr, BitVec.ofNat_add, BitVec.add_assoc]

def region (a : BitVec 64) (n : Nat) : MemoryRegion := ⟨a.toNat, n⟩

structure Input (code : CodeMap) (o : Ram) (s d : BitVec 64) (n : Nat) : Prop where
  src : Readable o s n
  dst : Writable code o d n
  apart : s.toNat + n ≤ d.toNat ∨ d.toNat + n ≤ s.toNat

structure Prefix (o m : Ram) (s d : BitVec 64) (n i : Nat) : Prop where
  frame : RamWriteFrame o m [region d n]
  copied : ∀ k < i, memByte m (ptr d k) = memByte o (ptr s k)

theorem start (o : Ram) (s d : BitVec 64) (n : Nat) : Prefix o o s d n 0 :=
  ⟨.refl .., by omega⟩

theorem guard {code o m s d n i} {count p : BitVec 64} {size k : Nat}
    (h : Input code o s d n) (pre : Prefix o m s d n i)
    (hl : i + size * count.toNat ≤ n)
    (hp : p.toNat + k ≤ 2^64)
    (hc : d.toNat + n ≤ p.toNat ∨ p.toNat + k ≤ d.toNat) :
    RepMovsOk code m 0 (ptr s i) (ptr d i) count size p k := by
  have := h.src.low
  have := h.dst.readable.low
  have hs := ptr_nat (a := s) (i := i) (by omega)
  have hd := ptr_nat (a := d) (i := i) (by omega)
  have sr := (h.src.of_frame pre.frame).sub (a := ptr s i) (n := size * count.toNat)
    (by omega) (by omega)
  have ds := (h.dst.of_frame pre.frame).sub (a := ptr d i) (n := size * count.toNat)
    (by omega) (by omega)
  exact ⟨rfl, sr.low, ds.readable.low, sr.present, ds.readable.present,
    by have := h.apart; omega, ds.tables, RangeApart.of_toNat (by omega) hp (by omega), ds.notCode⟩

private theorem byte_frame {o m : Ram} {r : MemoryRegion} (hf : RamWriteFrame o m [r])
    {a : BitVec 64} (hx : a.toNat + 1 ≤ r.start ∨ r.start + r.size ≤ a.toNat) :
    memByte m a = memByte o a := by
  have he := hf.outside a ⟨by have := a.isLt; omega, by simpa using hx⟩
  simp only [memByte, PhysicalMemory.read, he]

theorem advance {code o m s d n i} (h : Input code o s d n) (pre : Prefix o m s d n i)
    (l : Nat) (hl : i + l ≤ n) :
    Prefix o (memCopy m (ptr d i) (ptr s i) l) s d n (i+l) := by
  have := h.src.low
  have := h.dst.readable.low
  have hd := ptr_nat (a := d) (i := i) (by omega)
  let r := region (ptr d i) l
  have hf : RamWriteFrame m (memCopy m (ptr d i) (ptr s i) l) [r] := by
    apply (RamWriteFrame.refl m [r]).memStore
    refine ⟨r, .head _, ?_⟩
    simp only [r, region, InRegion]; omega
  constructor
  · apply pre.frame.trans hf
    intro z hz
    simp only [List.mem_singleton] at hz
    subst z
    exact ⟨region d n, .head _, by simp only [r, region]; omega, by simp only [r, region]; omega⟩
  · intro k hk
    have hdk := ptr_nat (a := d) (i := k) (by omega)
    by_cases hi : k < i
    · rw [byte_frame hf (a := ptr d k) (by simp only [r, region]; omega)]
      exact pre.copied k hi
    · let j := k - i
      have hj : i + j = k := by dsimp [j]; omega
      have hjl : j < 8 * l / 8 := by omega
      have he := memStore_getElem?_self_of_le m (ptr d i) (memLoad m (ptr s i) (8*l))
        (by omega) j hjl
      rw [storedByte_memLoad m (ptr s i) j hjl] at he
      change (memCopy m (ptr d i) (ptr s i) l)[ptr (ptr d i) j]? =
        some (memByte m (ptr (ptr s i) j)) at he
      rw [ptr_ptr, ptr_ptr, hj] at he
      have hsk := ptr_nat (a := s) (i := k) (by omega)
      have srcEq := byte_frame pre.frame (a := ptr s k) (by
        simp only [region]
        have := h.apart
        omega)
      simp only [memByte, PhysicalMemory.read, he] at *
      exact srcEq

end ChaCha20Poly1305.Proofs.Decrypt.Copy
