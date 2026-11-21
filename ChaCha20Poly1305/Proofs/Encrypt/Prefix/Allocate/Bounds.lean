import ChaCha20Poly1305.Proofs.Encrypt.Contract
import ChaCha20Poly1305.Proofs.Core.Segments.Lengths

namespace ChaCha20Poly1305.Proofs.Encrypt.Prefix

open ChaCha20Poly1305.Spec ChaCha20Poly1305.Spec.Program
open Standards.RFC.ChaCha20Poly1305 Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem allocation_bounds [Bindings] {initial : RamState}
    {key : Vector UInt8 32} {nonce : Vector UInt8 12} {aad plaintext : ByteArray}
    (hc : ValidCall encrypt initial [key, nonce, aad, plaintext]) :
    (initial.regValue .r8).toNat + (plaintext.size + 16) < 2 ^ 32 ∧
      initial.regValue .r8 ≠ 0 ∧
      plaintext.size + 16 ≤ (memLoad initial.external (stackPtr initial + 24) 64).toNat := by
  have hh := (hc.heapInMemory rfl).1.1
  rw [heap_region hc] at hh
  change (initial.regValue .r8).toNat + (plaintext.size + 16) < 2^32 at hh
  have hn := hc.heapNonzeroIfAllocating rfl
  rw [heap_region hc] at hn
  have hn' : (initial.regValue .r8).toNat ≠ 0 := hn (by simp [registerRegion])
  refine ⟨hh, fun hz => hn' (by rw [hz]; rfl), ?_⟩
  obtain ⟨cap, hcap, hlen⟩ := hc.heapLengthArgumentCoversHeap
    ⟨.r8, .stack 2, fun n => n + 16⟩ (by simp [encrypt])
  rw [heap_region hc] at hlen
  change plaintext.size + 16 ≤ cap.toNat at hlen
  have hv := Core.Lengths.word64At_memLoad hcap.2
  have hsp := hc.stackAvailable.2.2.1
  have htop := hc.stackAvailable.1
  change (stackPtr initial).toNat - 1168 +
    ((stackPtr initial).toNat + 8 - ((stackPtr initial).toNat - 1168)) < 2^32 at htop
  have he : BitVec.ofNat 64 (stackArgumentSlot initial 2).start = stackPtr initial + 24 := by
    apply BitVec.eq_of_toNat_eq
    change ((stackPtr initial).toNat + 8 * (2 + 1)) % 2^64 =
      ((stackPtr initial).toNat + 24) % 2^64
    rfl
  rw [he] at hv
  rw [hv]
  exact hlen

theorem allocation_limit {heap cap : BitVec 64} {length : Nat}
    (hlo : heap.toNat + (length + 16) < 2^32)
    (hcap : length + 16 ≤ cap.toNat) :
    (heap + BitVec.ofNat 64 (length + 16)).toNat ≤
      (if heap.toNat + cap.toNat < 2^64 then heap + cap else BitVec.allOnes 64).toNat := by
  have hv : (heap + BitVec.ofNat 64 (length + 16)).toNat = heap.toNat + length + 16 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [hv]
  split
  · simp only [BitVec.toNat_add]
    omega
  · simp only [BitVec.toNat_allOnes]
    omega

end ChaCha20Poly1305.Proofs.Encrypt.Prefix
