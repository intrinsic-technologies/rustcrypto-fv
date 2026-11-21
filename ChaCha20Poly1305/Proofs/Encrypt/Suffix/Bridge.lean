import ChaCha20Poly1305.Proofs.Encrypt.Append.Contract
import ChaCha20Poly1305.Proofs.Encrypt.Suffix.Facts
import ChaCha20Poly1305.Proofs.Encrypt.Suffix.Steps
import ChaCha20Poly1305.Proofs.Encrypt.Suffix.AppendPre
import ChaCha20Poly1305.Proofs.Encrypt.Suffix.Bytes

namespace ChaCha20Poly1305.Proofs.Encrypt.Suffix

open ChaCha20Poly1305.Spec ChaCha20Poly1305.Spec.Program
open Standards.RFC.ChaCha20Poly1305 Prelude X86 X86.Machine X86.UserProcess X86Proofs
open CoreContract Wrapper

theorem setup_frame [Bindings] {initial t u : RamState}
    (st : EntryStack initial) (T : GTrack (appendCs (stackPtr initial)) t u) :
    MemoryWriteFrame t u #v[Stack.region initial encrypt.minStackBytes] := by
  apply T.agrees.memoryWriteFrame
  intro c hc a ha
  simp only [appendCs, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  all_goals
    obtain ⟨i, hi, rfl⟩ := ha
    refine ⟨Stack.region initial encrypt.minStackBytes, by simp, ?_⟩
    change (stackPtr initial).toNat - 1168 ≤ _ ∧
      _ < (stackPtr initial).toNat - 1168 +
        ((stackPtr initial).toNat + 8 - ((stackPtr initial).toNat - 1168))
    have room := st.room
    first
    | change (stackPtr initial).toNat - 1168 ≤ (stackPtr initial - BitVec.ofNat 64 112 + BitVec.ofNat 64 i).toNat ∧
        (stackPtr initial - BitVec.ofNat 64 112 + BitVec.ofNat 64 i).toNat <
          (stackPtr initial).toNat - 1168 + ((stackPtr initial).toNat + 8 - ((stackPtr initial).toNat - 1168))
      rw [slot_toNat (k := 112) (by omega) st.top (by omega)]
      constructor <;> omega
    | change (stackPtr initial).toNat - 1168 ≤ (stackPtr initial - BitVec.ofNat 64 120 + BitVec.ofNat 64 i).toNat ∧
        (stackPtr initial - BitVec.ofNat 64 120 + BitVec.ofNat 64 i).toNat <
          (stackPtr initial).toNat - 1168 + ((stackPtr initial).toNat + 8 - ((stackPtr initial).toNat - 1168))
      rw [slot_toNat (k := 120) (by omega) st.top (by omega)]
      constructor <;> omega
    | change (stackPtr initial).toNat - 1168 ≤ (stackPtr initial - BitVec.ofNat 64 176 + BitVec.ofNat 64 i).toNat ∧
        (stackPtr initial - BitVec.ofNat 64 176 + BitVec.ofNat 64 i).toNat <
          (stackPtr initial).toNat - 1168 + ((stackPtr initial).toNat + 8 - ((stackPtr initial).toNat - 1168))
      rw [slot_toNat (k := 176) (by omega) st.top (by omega)]
      constructor <;> omega

theorem append_frame [Bindings] {initial u v : RamState}
    {key : Vector UInt8 32} {nonce : Vector UInt8 12} {aad msg : ByteArray}
    (hc : ValidCall encrypt initial [key, nonce, aad, msg])
    (rsp : stackPtr u = stackPtr initial - 176)
    (rdi : rd u 7 = stackPtr initial - 168)
    (post : AppendPost u v (initial.regValue .r8) msg.size
      (chacha20AeadEncrypt aad key nonce msg).2) :
    MemoryWriteFrame u v #v[heapRegion encrypt initial, Stack.region initial encrypt.minStackBytes] := by
  have room : 1168 ≤ (stackPtr initial).toNat := hc.stackAvailable.2.2.1
  have spi : (stackPtr u).toNat = (stackPtr initial).toNat - 176 := by
    rw [rsp]; exact slot_toNat0 (k := 176) (by omega)
  have di : (u.regValue .rdi).toNat = (stackPtr initial).toNat - 168 := by
    change (rd u 7).toNat = _
    rw [rdi]; exact slot_toNat0 (k := 168) (by omega)
  apply frame_widen post.frame
  intro r hr a ha
  simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · refine ⟨Stack.region initial encrypt.minStackBytes, by simp, ?_⟩
    change (Stack.region initial 1168).Contains a
    rw [stack_region_eq initial 1168 room]
    simp only [MemoryRegion.Contains, di] at ha ⊢
    omega
  · refine ⟨heapRegion encrypt initial, by simp, ?_⟩
    rw [heap_region hc]
    simp only [appendDestination, registerRegion, MemoryRegion.Contains] at ha ⊢
    omega
  · refine ⟨Stack.region initial encrypt.minStackBytes, by simp, ?_⟩
    change (Stack.region initial 1168).Contains a
    rw [stack_region_eq initial 1168 room]
    change (stackPtr u).toNat - 48 ≤ a ∧
      a < (stackPtr u).toNat - 48 + ((stackPtr u).toNat + 8 - ((stackPtr u).toNat - 48)) at ha
    rw [spi] at ha
    change (stackPtr initial).toNat - 1168 ≤ a ∧ a < (stackPtr initial).toNat - 1168 + 1176
    omega

theorem append_bytes [Bindings] {initial u v : RamState}
    {key : Vector UInt8 32} {nonce : Vector UInt8 12} {aad msg : ByteArray}
    (hc : ValidCall encrypt initial [key, nonce, aad, msg])
    (rsp : stackPtr u = stackPtr initial - 176)
    (rdi : rd u 7 = stackPtr initial - 168)
    (ct : (messageRegion (initial.regValue .r8) msg.size).HasBytes u.external
      (chacha20AeadEncrypt aad key nonce msg).1)
    (post : AppendPost u v (initial.regValue .r8) msg.size
      (chacha20AeadEncrypt aad key nonce msg).2) :
    (heapRegion encrypt initial).HasBytes v.external (AEAD.encryptWithTag aad key nonce msg) := by
  have room : 1168 ≤ (stackPtr initial).toNat := hc.stackAvailable.2.2.1
  have spi : (stackPtr u).toNat = (stackPtr initial).toNat - 176 := by
    rw [rsp]; exact slot_toNat0 (k := 176) (by omega)
  have di : (u.regValue .rdi).toNat = (stackPtr initial).toNat - 168 := by
    change (rd u 7).toNat = _
    rw [rdi]; exact slot_toNat0 (k := 168) (by omega)
  have heap := (hc.heapInMemory rfl).1
  rw [heap_region hc] at heap
  have bounded : (messageRegion (initial.regValue .r8) msg.size).Bounded := by
    change (initial.regValue .r8).toNat + msg.size < userAddressLimit
    have hb := heap.1
    change (initial.regValue .r8).toNat + (msg.size + 16) < userAddressLimit at hb
    omega
  have pair := hc.separation.1
  have wr : writtenRegions encrypt initial [key, nonce, aad, msg] =
      [bufferRegion encrypt initial, heapRegion encrypt initial, allocatorStateRegion,
        Stack.region initial 1168] := rfl
  rw [wr] at pair
  have hs := (List.pairwise_cons.mp pair.tail).1 (Stack.region initial 1168) (by simp)
  rw [heap_region hc] at hs
  have kept := hasBytes_frame post.frame bounded (by
    intro w hw x hx hm
    have inheap : (registerRegion initial .r8 (msg.size + 16)).Contains x := by
      simp only [registerRegion, messageRegion, MemoryRegion.Contains] at hm ⊢
      omega
    simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · apply hs x inheap
      rw [stack_region_eq initial 1168 room]
      simp only [MemoryRegion.Contains, di] at hx ⊢
      omega
    · simp only [appendDestination, messageRegion, MemoryRegion.Contains] at hx hm
      omega
    · apply hs x inheap
      rw [stack_region_eq initial 1168 room]
      change (stackPtr u).toNat - 48 ≤ x ∧
        x < (stackPtr u).toNat - 48 + ((stackPtr u).toNat + 8 - ((stackPtr u).toNat - 48)) at hx
      rw [spi] at hx
      change (stackPtr initial).toNat - 1168 ≤ x ∧ x < (stackPtr initial).toNat - 1168 + 1176
      omega) ct
  rw [heap_region hc]
  exact hasBytes_append kept post.tag

theorem saved_word [Bindings] {initial s t u v : RamState}
    {key : Vector UInt8 32} {nonce : Vector UInt8 12} {aad msg : ByteArray}
    (hc : ValidCall encrypt initial [key, nonce, aad, msg])
    (atCore : AtCore initial s msg.size)
    (core : CorePost s t key nonce aad msg (initial.regValue .r8))
    (T : GTrack (appendCs (stackPtr initial)) t u)
    (rsp : stackPtr u = stackPtr initial - 176) (rdi : rd u 7 = stackPtr initial - 168)
    (post : AppendPost u v (initial.regValue .r8) msg.size
      (chacha20AeadEncrypt aad key nonce msg).2)
    {k : Nat} (hk : k ≤ 48) {value : BitVec 64}
    (word : (localWord initial k).Word64At s.external value) :
    wd v (stackPtr initial - BitVec.ofNat 64 k) = value := by
  rw [append_post_word_kept hc rsp rdi post (by omega) (by omega),
    append_word_kept T (by omega) (by omega), core_word_kept hc atCore core (by omega) (by omega)]
  have h := word64At_memLoad word
  have st := entry_stack hc
  have addr : BitVec.ofNat 64 (localWord initial k).start =
      stackPtr initial - BitVec.ofNat 64 k := by
    apply BitVec.eq_of_toNat_eq
    change ((stackPtr initial).toNat - k) % 2^64 = _
    rw [slot_toNat0 (by have := st.room; omega)]
    have := st.top
    omega
  rw [addr] at h
  exact h

end ChaCha20Poly1305.Proofs.Encrypt.Suffix
