import ChaCha20Poly1305.Proofs.Decrypt.Entry

namespace ChaCha20Poly1305.Proofs.Decrypt

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.Refine Prelude
open ChaCha20Poly1305.Spec.Program

theorem apart_ends {r q : MemoryRegion} (hd : r.Disjoint q) (hr : 0 < r.size) (hq : 0 < q.size) :
    r.start + r.size ≤ q.start ∨ q.start + q.size ≤ r.start := by
  apply Classical.byContradiction
  intro hn
  apply hd (max r.start q.start)
  all_goals simp only [MemoryRegion.Contains, Nat.max_def]; split <;> omega

theorem stack_text_apart {s : RamState} {inputs : List ByteArray} (h : ValidCall decrypt s inputs) :
    (s.regValue .rsp).toNat ≤ 0x100000 ∨ 0x102def + 1008 ≤ (s.regValue .rsp).toNat := by
  let stack := Stack.region s decrypt.minStackBytes
  let text : MemoryRegion := ⟨0x100000, 0x2def⟩
  have ha := h.separation.2.2 stack (by simp [stack, writtenRegions])
  have hd : stack.Disjoint text := by
    intro a hs ht
    have hb : a < 2^64 := by
      have : a < 0x100000 + 0x2def := ht.2
      omega
    let b := BitVec.ofNat 64 a
    have he : b.toNat = a := Nat.mod_eq_of_lt hb
    apply ha b (he ▸ hs)
    left
    obtain ⟨v, hv⟩ := exists_mem_toCodeMap (sections := Lifted.sections) (s := Lifted.textSection)
      (.head _) (a := b) (by rw [he]; exact ht.1) (by rw [he]; exact ht.2)
    exact ⟨v, loaded_text hv⟩
  have hsp : 1136 ≤ (s.regValue .rsp).toNat := h.stackAvailable.2.2.1
  have hp : 0 < stack.size := by
    change 0 < (s.regValue .rsp).toNat + 8 - ((s.regValue .rsp).toNat - 1136)
    omega
  have hv := apart_ends hd hp (by decide)
  change _ - 1136 + ((s.regValue .rsp).toNat + 8 - (_ - 1136)) ≤ 0x100000 ∨
    0x100000 + 0x2def ≤ (s.regValue .rsp).toNat - 1136 at hv
  omega

theorem allocator_writable {s : RamState} {inputs : List ByteArray} (h : ValidCall decrypt s inputs) :
    Writable Lifted.fnCode s.external 0x300000 16 := by
  apply Writable.of_avoids (region := allocatorStateRegion) (forbidden := Forbidden) (by change 0x300000 + 16 < 2^32; decide)
    (h.heapInMemory rfl).2 _ code_forbidden tables_forbidden (by decide) (by decide) (by decide)
  apply h.separation.2.2
  simp [writtenRegions, decrypt]

theorem call_apart {s : RamState} {key : Vector UInt8 32} {nonce : Vector UInt8 12}
    {aad msg : ByteArray} (h : ValidCall decrypt s [key, nonce, aad, msg]) :
    let rsp := (s.regValue .rsp).toNat
    let k := (s.regValue .rdi).toNat
    (k + 32 ≤ rsp - 1008 ∨ rsp + 8 ≤ k) ∧
    (k + 32 ≤ 0x300000 ∨ 0x300010 ≤ k) ∧
    (rsp + 8 ≤ 0x300000 ∨ 0x300010 ≤ rsp - 1008) ∧
    (rsp + 32 ≤ 0x300000 ∨ 0x300010 ≤ rsp + 16) := by
  let written := writtenRegions decrypt s [key, nonce, aad, msg]
  let read := readRegions decrypt s [key, nonce, aad, msg]
  let stack := Stack.region s decrypt.minStackBytes
  let kr := registerRegion s .rdi 32
  have hw : stack ∈ written := by simp [written, writtenRegions, stack]
  have hg : allocatorStateRegion ∈ written := by simp [written, writtenRegions, decrypt]
  have hk : kr ∈ read := by simp [read, readRegions, decrypt, inputRegion, kr]
  have slot1 : stackArgumentSlot s 1 ∈ read := by simp [read, readRegions, decrypt, argumentRegions]
  have slot2 : stackArgumentSlot s 2 ∈ read := by simp [read, readRegions, decrypt, argumentRegions]
  have hsp : 1136 ≤ (s.regValue .rsp).toNat := h.stackAvailable.2.2.1
  have pos : 0 < stack.size := by change 0 < _ + 8 - ((s.regValue .rsp).toNat - 1136); omega
  have gs : allocatorStateRegion.Disjoint stack := by
    have hp := h.separation.1
    rw [writtenRegions] at hp
    split at hp
    · exact (List.pairwise_cons.mp hp.tail.tail).1 _ (.head _)
    · exact (List.pairwise_cons.mp hp.tail).1 _ (.head _)
  have h1 := apart_ends (h.separation.2.1 _ hw _ hk) pos (Nat.zero_lt_succ _)
  have h2 := apart_ends (h.separation.2.1 _ hg _ hk) (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
  have h3 := apart_ends gs (Nat.zero_lt_succ _) pos
  have h4 := apart_ends (h.separation.2.1 _ hg _ slot1) (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
  have h5 := apart_ends (h.separation.2.1 _ hg _ slot2) (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
  simp only [stack, kr, registerRegion, allocatorStateRegion, Stack.region, Stack.returnAddressBytes,
    decrypt, stackArgumentSlot] at h1 h2 h3 h4 h5
  dsimp only
  omega

end ChaCha20Poly1305.Proofs.Decrypt
