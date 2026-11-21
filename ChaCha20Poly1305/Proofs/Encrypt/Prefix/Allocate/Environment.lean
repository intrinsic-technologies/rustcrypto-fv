import ChaCha20Poly1305.Proofs.Encrypt.Prefix.Allocate.Preserve
import ChaCha20Poly1305.Proofs.Common.WritableRange

namespace ChaCha20Poly1305.Proofs.Encrypt.Prefix

open ChaCha20Poly1305.Spec ChaCha20Poly1305.Spec.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs Wrapper

theorem heap_writable {initial s : RamState} {key : Vector UInt8 32} {nonce : Vector UInt8 12}
    {aad msg : ByteArray} (hc : ValidCall encrypt initial [key, nonce, aad, msg])
    (hg : Grows initial s) :
    ChaCha20Poly1305.Proofs.Common.WritableRange s (initial.regValue .r8) msg.size := by
  have hh := (hc.heapInMemory rfl).1
  rw [heap_region hc] at hh
  have hlo : (initial.regValue .r8).toNat + (msg.size + 16) < 2^32 := hh.1
  have mem : heapRegion encrypt initial ∈ writtenRegions encrypt initial [key, nonce, aad, msg] := by
    simp [writtenRegions, encrypt]
  have covers (i : Nat) (hi : i < msg.size) :
      (heapRegion encrypt initial).Contains (initial.regValue .r8 + BitVec.ofNat 64 i).toNat := by
    rw [heap_region hc]
    change (initial.regValue .r8).toNat ≤ _ ∧ _ < (initial.regValue .r8).toNat + (msg.size + 16)
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  refine ⟨⟨by omega, fun i hi => hg _ ?_⟩, ?_, ?_⟩
  · obtain ⟨v, hv⟩ := hh.2 _ (by rw [← heap_region hc]; exact covers i hi)
    simp only [hv, Option.isSome_some]
  · intro i hi hp
    exact hc.separation.2.2 _ mem _ (covers i hi) (Or.inr hp)
  · intro i hi hp
    exact hc.separation.2.2 _ mem _ (covers i hi) (Or.inl hp)

theorem input_readable {s : RamState} {p : BitVec 64} {bytes : ByteArray}
    (h : ValidInput s ⟨p.toNat, bytes.size⟩ bytes) : MemReadable s p bytes.size := by
  have hb : p.toNat + bytes.size < 2^32 := h.1
  refine ⟨by omega, fun i hi => ?_⟩
  have he : BitVec.ofNat 64 (p.toNat + i) = p + BitVec.ofNat 64 i := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hv := h.2.2 ⟨i, hi⟩
  change s.external[BitVec.ofNat 64 (p.toNat + i)]? = _ at hv
  rw [he] at hv
  simp only [hv, Option.isSome_some]

theorem input_heap_disjoint {initial : RamState} {key : Vector UInt8 32} {nonce : Vector UInt8 12}
    {aad msg : ByteArray} (hc : ValidCall encrypt initial [key, nonce, aad, msg]) (hn : 0 < msg.size) :
    (initial.regValue .rcx).toNat + msg.size ≤ (initial.regValue .r8).toNat ∨
      (initial.regValue .r8).toNat + msg.size ≤ (initial.regValue .rcx).toNat := by
  have h := hc.separation.2.1 (heapRegion encrypt initial) (by simp [writtenRegions, encrypt])
    (registerRegion initial .rcx msg.size) (by simp [readRegions, encrypt, inputRegion])
  rw [heap_region hc] at h
  have sep := region_sep h (by change 0 < msg.size + 16; omega) hn
  change (initial.regValue .r8).toNat + (msg.size + 16) ≤ (initial.regValue .rcx).toNat ∨
    (initial.regValue .rcx).toNat + msg.size ≤ (initial.regValue .r8).toNat at sep
  omega


theorem heap_stack_disjoint {initial : RamState} {key : Vector UInt8 32} {nonce : Vector UInt8 12}
    {aad msg : ByteArray} (hc : ValidCall encrypt initial [key, nonce, aad, msg]) :
    (heapRegion encrypt initial).Disjoint (Stack.region initial 1168) := by
  have h := hc.separation.1
  change List.Pairwise MemoryRegion.Disjoint
    [bufferRegion encrypt initial, heapRegion encrypt initial, allocatorStateRegion,
      Stack.region initial 1168] at h
  exact (List.pairwise_cons.mp h.tail).1 _ (by simp)

end ChaCha20Poly1305.Proofs.Encrypt.Prefix
