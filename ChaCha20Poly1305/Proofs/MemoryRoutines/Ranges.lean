import ChaCha20Poly1305.Proofs.MemoryRoutines.Contracts

namespace ChaCha20Poly1305.Proofs.MemoryRoutines

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.Common

theorem rangeApart_slice_left {a b : BitVec 64} {m n : Nat} (h : RangeApart a m b n)
    (offset count : Nat) (hle : offset + count ≤ m) :
    RangeApart (a + BitVec.ofNat 64 offset) count b n := by
  intro i hi j hj
  rw [add_ofNat_add_ofNat]
  exact h (offset + i) (by omega) j hj

theorem rangeApart_slice_right {a b : BitVec 64} {m n : Nat} (h : RangeApart a m b n)
    (offset count : Nat) (hle : offset + count ≤ n) :
    RangeApart a m (b + BitVec.ofNat 64 offset) count := by
  intro i hi j hj
  rw [add_ofNat_add_ofNat]
  exact h i hi (offset + j) (by omega)

theorem copy_append {s t u : RamState} {dst src : BitVec 64} {head tail : Nat}
    (hhead : ∀ i < head, t.external[dst + BitVec.ofNat 64 i]? =
      s.external[src + BitVec.ofNat 64 i]?)
    (htail : ∀ i < tail,
      u.external[dst + BitVec.ofNat 64 head + BitVec.ofNat 64 i]? =
      t.external[src + BitVec.ofNat 64 head + BitVec.ofNat 64 i]?)
    (hsrc : ∀ i < tail,
      t.external[src + BitVec.ofNat 64 head + BitVec.ofNat 64 i]? =
      s.external[src + BitVec.ofNat 64 head + BitVec.ofNat 64 i]?)
    (hframe : ∀ i < head, u.external[dst + BitVec.ofNat 64 i]? =
      t.external[dst + BitVec.ofNat 64 i]?) :
    ∀ i < head + tail, u.external[dst + BitVec.ofNat 64 i]? =
      s.external[src + BitVec.ofNat 64 i]? := by
  intro i hi
  by_cases h : i < head
  · exact (hframe i h).trans (hhead i h)
  · have hle : head ≤ i := by omega
    have hc := (htail (i - head) (by omega)).trans (hsrc (i - head) (by omega))
    simpa only [add_ofNat_add_ofNat, Nat.add_sub_cancel' hle] using hc

end ChaCha20Poly1305.Proofs.MemoryRoutines
