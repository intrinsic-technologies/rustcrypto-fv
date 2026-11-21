import ChaCha20Poly1305.Proofs.Encrypt.Append.Contract
import ChaCha20Poly1305.Proofs.Encrypt.Suffix.Steps
import ChaCha20Poly1305.Proofs.Encrypt.Suffix.Facts

namespace ChaCha20Poly1305.Proofs.Encrypt.Suffix

open ChaCha20Poly1305.Spec ChaCha20Poly1305.Spec.Program
open Standards.RFC.ChaCha20Poly1305 Prelude X86 X86.Machine X86.UserProcess X86Proofs
open CoreContract Wrapper

theorem append_word_kept [Bindings] {initial t u : RamState}
    (T : GTrack (appendCs (stackPtr initial)) t u)
    {k : Nat} (hk : k ≤ 168) (ha : k ≤ 104 ∨ 128 ≤ k) :
    wd u (stackPtr initial - BitVec.ofNat 64 k) =
      wd t (stackPtr initial - BitVec.ofNat 64 k) := by
  apply gload T.agrees
  intro c hc i hi
  simp only [appendCs, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact fun h => h
  · exact slot_not_covers (k' := 112) hi (by omega) (by omega) (by omega)
  · exact slot_not_covers (k' := 120) hi (by omega) (by omega) (by omega)
  · exact slot_not_covers (k' := 176) hi (by omega) (by omega) (by omega)

set_option maxRecDepth 4096 in
theorem append_pre [bindings : Bindings] {initial s t u : RamState}
    {key : Vector UInt8 32} {nonce : Vector UInt8 12} {aad msg : ByteArray}
    (hc : ValidCall encrypt initial [key, nonce, aad, msg])
    (atCore : AtCore initial s msg.size)
    (post : CorePost s t key nonce aad msg (initial.regValue .r8))
    (T : GTrack (appendCs (stackPtr initial)) t u)
    (hrip : u.RIP = 0x101fb0) (hsp : stackPtr u = stackPtr initial - 176)
    (hdi : rd u 7 = stackPtr initial - 168) (hsi : rd u 6 = stackPtr initial - 120)
    (hdx : rd u 2 = 16)
    (hw0 : wd u (stackPtr initial - 120) = wd t (stackPtr initial - 136))
    (hw8 : wd u (stackPtr initial - 112) = wd t (stackPtr initial - 128)) :
    AppendPre u (initial.regValue .r8) msg.size (chacha20AeadEncrypt aad key nonce msg).2 := by
  have st := entry_stack hc
  have room := st.room
  have top := st.top
  have addrNat : ∀ k i : Nat, k ≤ 1104 → i < k + 8 →
      BitVec.ofNat 64 ((stackPtr initial).toNat - k + i) =
        stackPtr initial - BitVec.ofNat 64 k + BitVec.ofNat 64 i := by
    intro k i hk hi
    apply BitVec.eq_of_toNat_eq
    rw [slot_toNat (by omega) top hi, BitVec.toNat_ofNat]
    omega
  have grows : Grows initial u := (show Grows initial t from fun a ha =>
    post.grows a (atCore.grows a ha)).step T.agrees
  have spi : (u.regValue .rsp).toNat = (stackPtr initial).toNat - 176 := by
    change (stackPtr u).toNat = _
    rw [hsp]; exact slot_toNat0 (k := 176) (by omega)
  have di : (u.regValue .rdi).toNat = (stackPtr initial).toNat - 168 := by
    change (rd u 7).toNat = _
    rw [hdi]; exact slot_toNat0 (k := 168) (by omega)
  have si : (u.regValue .rsi).toNat = (stackPtr initial).toNat - 120 := by
    change (rd u 6).toNat = _
    rw [hsi]; exact slot_toNat0 (k := 120) (by omega)
  have sr : Stack.region u 48 = ⟨(stackPtr initial).toNat - 224, 56⟩ := by
    simp only [Stack.region, Stack.returnAddressBytes, spi, MemoryRegion.mk.injEq]
    constructor <;> omega
  have dr : appendDescriptor u = ⟨(stackPtr initial).toNat - 168, 24⟩ := by
    simp only [appendDescriptor, registerRegion, di]
  have tr : appendSource u = ⟨(stackPtr initial).toNat - 120, 16⟩ := by
    simp only [appendSource, registerRegion, si]
  have heap := (hc.heapInMemory (by rfl)).1
  rw [heap_region hc] at heap
  have bound : (initial.regValue .r8).toNat + msg.size + 16 < userAddressLimit := by
    have := heap.1; change (initial.regValue .r8).toNat + (msg.size + 16) < _ at this; omega
  have wr : writtenRegions encrypt initial [key, nonce, aad, msg] =
      [bufferRegion encrypt initial, heapRegion encrypt initial, allocatorStateRegion,
        Stack.region initial 1168] := rfl
  have pair := hc.separation.1
  rw [wr] at pair
  have hs := (List.pairwise_cons.mp pair.tail).1 (Stack.region initial 1168) (by simp)
  rw [heap_region hc] at hs
  have substack : ∀ (r : MemoryRegion), (stackPtr initial).toNat - 1104 ≤ r.start →
      r.start + r.size ≤ (stackPtr initial).toNat + 8 →
      ∀ x, r.Contains x → (Stack.region initial 1168).Contains x := by
    intro r h1 h2 x hx
    change (stackPtr initial).toNat - 1168 ≤ x ∧ x < _
    simp only [MemoryRegion.Contains] at hx
    change _ ∧ x < (stackPtr initial).toNat - 1168 +
      ((stackPtr initial).toNat + 8 - ((stackPtr initial).toNat - 1168))
    constructor <;> omega
  have subheap : ∀ x, (appendDestination (initial.regValue .r8) msg.size).Contains x →
      (registerRegion initial .r8 (msg.size + 16)).Contains x := by
    intro x hx
    simp only [appendDestination, registerRegion, MemoryRegion.Contains] at hx ⊢
    constructor <;> omega
  have hsD := disjoint_mono hs subheap (substack (⟨(stackPtr initial).toNat - 168, 24⟩) (by simp; omega) (by simp; omega))
  have hsS := disjoint_mono hs subheap (substack (⟨(stackPtr initial).toNat - 224, 56⟩)
    (by simp; omega) (by simp; omega))
  have hsT := disjoint_mono hs subheap (substack (⟨(stackPtr initial).toNat - 120, 16⟩)
    (by simp; omega) (by simp; omega))
  have keep : ∀ k, k ≤ 168 → (k ≤ 104 ∨ 145 ≤ k) →
      wd u (stackPtr initial - BitVec.ofNat 64 k) = wd s (stackPtr initial - BitVec.ofNat 64 k) := by
    intro k hk ha
    rw [append_word_kept T hk (by omega), core_word_kept hc atCore post hk (by omega)]
  refine
    { environment := ⟨T.ready.smrr, T.ready.memoryType, post.environment.stringStride,
      T.ready.features.lzcnt⟩
      machine := ⟨T.ready.cpu, SupportedSSE.of_agreesExcept T.agrees post.machine.sse,
      T.ready.memory, T.ready.ready⟩
      code := T.code, entry := hrip
      directionFlagUnset := T.agrees.directionFlagClear (by simp [appendCs]) post.directionFlagUnset
      stack := ?_, count := hdx, lengthBound := bound, descriptor := ?_
      capacity := ?_, pointer := ?_, lengthWord := ?_, source := ?_, destination := ?_, separation := ?_ }
  · have al := hc.stackAvailable.2.2.2
    simp only [Stack.returnSlot, MemoryRegion.Aligned, Stack.callAlignment,
      Stack.returnAddressBytes] at al
    change (stackPtr initial).toNat % 16 = 8 at al
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [sr]; change (stackPtr initial).toNat - 224 + 56 < userAddressLimit; unfold userAddressLimit; omega
    · rw [sr]; exact stack_allocated st grows (by simp; omega) (by simp; omega)
    · change 48 ≤ (u.regValue .rsp).toNat; rw [spi]; omega
    · simp only [Stack.returnSlot, MemoryRegion.Aligned, Stack.callAlignment,
        Stack.returnAddressBytes, spi]; omega
  · rw [dr]; exact ⟨by change (stackPtr initial).toNat - 168 + 24 < userAddressLimit; unfold userAddressLimit; omega,
      stack_allocated st grows (by simp; omega) (by simp; omega)⟩
  · apply slot_word st grows (k := 168) (by omega) (by omega) _ (by rw [di])
    rw [keep 168 (by omega) (by omega)]
    have h := word64At_memLoad atCore.capacity
    have addr : BitVec.ofNat 64 (localWord initial 168).start = stackPtr initial - BitVec.ofNat 64 168 := by
      simpa only [localWord, Nat.add_zero, BitVec.add_zero] using
        addrNat 168 0 (by omega) (by omega)
    rw [addr] at h
    exact h
  · apply slot_word st grows (k := 160) (by omega) (by omega) _ (by rw [di]; omega)
    rw [keep 160 (by omega) (by omega)]
    have h := word64At_memLoad atCore.pointer
    have addr : BitVec.ofNat 64 (localWord initial 160).start = stackPtr initial - BitVec.ofNat 64 160 := by
      simpa only [localWord, Nat.add_zero, BitVec.add_zero] using
        addrNat 160 0 (by omega) (by omega)
    rw [addr] at h
    exact h
  · apply slot_word st grows (k := 152) (by omega) (by omega) _ (by rw [di]; omega)
    rw [keep 152 (by omega) (by omega)]
    have h := word64At_memLoad atCore.lengthWord
    have addr : BitVec.ofNat 64 (localWord initial 152).start = stackPtr initial - BitVec.ofNat 64 152 := by
      simpa only [localWord, Nat.add_zero, BitVec.add_zero] using
        addrNat 152 0 (by omega) (by omega)
    rw [addr] at h
    exact h
  · rw [tr]
    refine ⟨by change (stackPtr initial).toNat - 120 + 16 < userAddressLimit; unfold userAddressLimit; omega, by simp [MemoryRegion.HasLength, ByteArray.size], ?_⟩
    intro i
    have hi : i.val < 16 := by simpa [ByteArray.size] using i.isLt
    have tag := post.tag.2 i
    have rdi : (s.regValue .rdi).toNat = (stackPtr initial).toNat - 137 := by
      rw [atCore.result]; exact slot_toNat0 (k := 137) (by omega)
    simp only [rdi] at tag
    by_cases h : i.val < 8
    · rw [addrNat 120 i.val (by omega) (by omega)]
      apply copied_byte (fun o ho => (stack_readable st grows (k := 120) (n := 8) (by omega) (by omega)).2 o ho) hw0 h
      rw [show (stackPtr initial).toNat - 137 + 1 + i.val = (stackPtr initial).toNat - 136 + i.val by omega,
        addrNat 136 i.val (by omega) (by omega)] at tag
      exact tag
    · rw [show (stackPtr initial).toNat - 120 + i.val = (stackPtr initial).toNat - 112 + (i.val - 8) by omega,
        addrNat 112 (i.val - 8) (by omega) (by omega)]
      apply copied_byte (fun o ho => (stack_readable st grows (k := 112) (n := 8) (by omega) (by omega)).2 o ho) hw8 (by omega)
      rw [show (stackPtr initial).toNat - 137 + 1 + i.val = (stackPtr initial).toNat - 128 + (i.val - 8) by omega,
        addrNat 128 (i.val - 8) (by omega) (by omega)] at tag
      exact tag
  · refine ⟨bound, ?_⟩
    intro a ha
    exact allocated_kept grows heap.2 a (subheap _ ha)
  · rw [dr, sr, tr]
    have avS := hc.separation.2.2 (Stack.region initial 1168) (by rw [wr]; simp)
    have avH := hc.separation.2.2 (heapRegion encrypt initial) (by rw [wr]; simp)
    rw [heap_region hc] at avH
    refine ⟨?_, ?_, ?_⟩
    · refine List.pairwise_cons.mpr ⟨?_, List.pairwise_cons.mpr ⟨?_, by simp⟩⟩
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact fun x hx hy => hsD x hy hx
        · exact disjoint_of_sep (by right; simp; omega)
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl
        exact hsS
    · intro r hr q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr hq
      rcases hq with rfl
      rcases hr with rfl | rfl | rfl
      · exact disjoint_of_sep (by left; simp; omega)
      · exact hsT
      · exact disjoint_of_sep (by left; simp; omega)
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact avoids_mono avS (substack _ (by simp; omega) (by simp; omega))
      · exact avoids_mono avH subheap
      · exact avoids_mono avS (substack _ (by simp; omega) (by simp; omega))

theorem append_post_word_kept [bindings : Bindings] {initial u v : RamState}
    {key : Vector UInt8 32} {nonce : Vector UInt8 12} {aad msg : ByteArray}
    {tag : Vector UInt8 16}
    (hc : ValidCall encrypt initial [key, nonce, aad, msg])
    (hsp : stackPtr u = stackPtr initial - 176)
    (hdi : rd u 7 = stackPtr initial - 168)
    (post : AppendPost u v (initial.regValue .r8) msg.size tag)
    {k : Nat} (hk : k ≤ 168) (apart : k ≤ 144 ∨ 160 ≤ k) :
    wd v (stackPtr initial - BitVec.ofNat 64 k) =
      wd u (stackPtr initial - BitVec.ofNat 64 k) := by
  have st := entry_stack hc
  have room := st.room
  have top := st.top
  have spi : (u.regValue .rsp).toNat = (stackPtr initial).toNat - 176 := by
    change (stackPtr u).toNat = _
    rw [hsp]; exact slot_toNat0 (k := 176) (by omega)
  have di : (u.regValue .rdi).toNat = (stackPtr initial).toNat - 168 := by
    change (rd u 7).toNat = _
    rw [hdi]; exact slot_toNat0 (k := 168) (by omega)
  have pair := hc.separation.1
  have wr : writtenRegions encrypt initial [key, nonce, aad, msg] =
      [bufferRegion encrypt initial, heapRegion encrypt initial, allocatorStateRegion,
        Stack.region initial 1168] := rfl
  rw [wr] at pair
  have hs := (List.pairwise_cons.mp pair.tail).1 (Stack.region initial 1168) (by simp)
  rw [heap_region hc] at hs
  apply wd_congr
  intro i hi
  have ai := slot_toNat (I := stackPtr initial) (k := k) (i := i) (by omega) top (by omega)
  apply post.frame
  intro r hr ar
  simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · simp only [MemoryRegion.Contains, di, ai] at ar
    omega
  · apply hs (stackPtr initial - BitVec.ofNat 64 k + BitVec.ofNat 64 i).toNat
    · simp only [appendDestination, MemoryRegion.Contains] at ar
      change (initial.regValue .r8).toNat ≤ _ ∧ _ < (initial.regValue .r8).toNat + (msg.size + 16)
      constructor <;> omega
    · change (stackPtr initial).toNat - 1168 ≤ _ ∧
        _ < (stackPtr initial).toNat - 1168 +
          ((stackPtr initial).toNat + 8 - ((stackPtr initial).toNat - 1168))
      rw [ai]
      constructor <;> omega
  · simp only [Stack.region, Stack.returnAddressBytes, MemoryRegion.Contains, spi, ai] at ar
    omega

end ChaCha20Poly1305.Proofs.Encrypt.Suffix
