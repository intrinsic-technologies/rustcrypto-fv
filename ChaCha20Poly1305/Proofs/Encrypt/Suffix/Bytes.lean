import ChaCha20Poly1305.Proofs.MemoryContracts

namespace ChaCha20Poly1305.Proofs.Encrypt.Suffix

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open ChaCha20Poly1305.Proofs.MemoryRoutines

theorem hasBytes_append {m : Ram} {start n k : Nat} {a b : ByteArray}
    (ha : (⟨start, n⟩ : MemoryRegion).HasBytes m a)
    (hb : (⟨start + n, k⟩ : MemoryRegion).HasBytes m b) :
    (⟨start, n + k⟩ : MemoryRegion).HasBytes m (a ++ b) := by
  have la : a.size = n := ha.1
  have lb : b.size = k := hb.1
  refine ⟨?_, ?_⟩
  · change (a ++ b).size = n + k
    rw [ByteArray.size_append, la, lb]
  · intro i
    by_cases hi : i.val < n
    · rw [ByteArray.getElem_append_left (by omega)]
      exact ha.2 ⟨i.val, by omega⟩
    · rw [ByteArray.getElem_append_right (by omega)]
      have h := hb.2 ⟨i.val - n, by have := i.isLt; simp only [ByteArray.size_append] at this; omega⟩
      simp only at h ⊢
      simpa only [la, show start + n + (i.val - n) = start + i.val by omega] using h

theorem memcpy_hasBytes [Bindings] {s t : RamState} {bytes : ByteArray}
    (post : MemcpyResult s t)
    (source : (⟨(rsi.read s).toNat, (rdx.read s).toNat⟩ : MemoryRegion).HasBytes
      s.external bytes) :
    (destination s).HasBytes t.external bytes := by
  refine ⟨source.1, ?_⟩
  intro i
  have hi : i.val < (rdx.read s).toNat := by
    have := i.isLt
    have : bytes.size = (rdx.read s).toNat := source.1
    omega
  have h := post.copy i.val hi
  have hb := source.2 i
  simp only [destination]
  have dst : BitVec.ofNat 64 ((rdi.read s).toNat + i.val) =
      rdi.read s + BitVec.ofNat 64 i.val := by
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have src : BitVec.ofNat 64 ((rsi.read s).toNat + i.val) =
      rsi.read s + BitVec.ofNat 64 i.val := by
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [dst, h]
  simpa only [src] using hb

theorem hasBytes_frame {s t : RamState} {r : MemoryRegion} {bytes : ByteArray}
    {n : Nat} {writes : Vector MemoryRegion n}
    (frame : MemoryWriteFrame s t writes) (bounded : r.Bounded)
    (apart : ∀ w ∈ writes, w.Disjoint r) (h : r.HasBytes s.external bytes) :
    r.HasBytes t.external bytes := by
  refine ⟨h.1, ?_⟩
  intro i
  rw [frame _ ?_]
  · exact h.2 i
  · intro w hw inside
    apply apart w hw _ inside
    have size : bytes.size = r.size := h.1
    have ilt := i.isLt
    change r.start + r.size < userAddressLimit at bounded
    rw [MemoryRegion.Contains, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by unfold userAddressLimit at bounded; omega)]
    constructor <;> omega

end ChaCha20Poly1305.Proofs.Encrypt.Suffix
