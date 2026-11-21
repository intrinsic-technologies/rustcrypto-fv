import ChaCha20Poly1305.Proofs.Encrypt.Contract
import ChaCha20Poly1305.Proofs.Wrapper

namespace ChaCha20Poly1305.Proofs.Encrypt.Suffix

open ChaCha20Poly1305.Spec ChaCha20Poly1305.Spec.Program
open Standards.RFC.ChaCha20Poly1305 Prelude X86 X86.Machine X86.UserProcess X86Proofs
open CoreContract Wrapper

set_option maxRecDepth 8000 in
theorem entry_stack {initial : RamState}
    {key : Vector UInt8 32} {nonce : Vector UInt8 12} {associatedData plaintext : ByteArray}
    (hCall : ValidCall encrypt initial [key, nonce, associatedData, plaintext]) :
    EntryStack initial := by
  have hv : Stack.Valid initial 1168 := hCall.stackAvailable
  obtain ⟨hb, ha, hn, -⟩ := hv
  have hav := hCall.separation.2.2 (Stack.region initial 1168) (by simp [writtenRegions, encrypt])
  simp only [Stack.region, MemoryRegion.Bounded, userAddressLimit, MemoryRegion.Allocated,
    MemoryRegion.Contains, Stack.NoUnderflow, Stack.returnAddressBytes] at hb ha hn
  simp only [MemoryRegion.Avoids, Stack.region, MemoryRegion.Contains, pageTables,
    Stack.returnAddressBytes] at hav
  have hsp : initial.regValue .rsp = stackPtr initial := rfl
  rw [hsp] at hb ha hn hav
  refine ⟨by omega, by omega, ?_, ?_, ?_⟩
  · intro a h1 h2
    obtain ⟨b, hb⟩ := ha a ⟨by omega, by omega⟩
    simp [hb]
  · intro a h1 h2 hp
    exact hav a ⟨by omega, by omega⟩ (.inl hp)
  · refine Classical.byContradiction fun hc => ?_
    let x : Nat := max ((stackPtr initial).toNat - 1104) 0x1000
    have hx : x < 2 ^ 64 := by omega
    apply hav (BitVec.ofNat 64 x)
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]
      constructor <;> omega
    · right
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]
      constructor <;> omega

theorem core_stack_kept [bindings : Bindings] {initial s t : RamState}
    {key : Vector UInt8 32} {nonce : Vector UInt8 12} {aad msg : ByteArray}
    (hc : ValidCall encrypt initial [key, nonce, aad, msg])
    (atCore : AtCore initial s msg.size)
    (post : CorePost s t key nonce aad msg (initial.regValue .r8))
    (a : BitVec 64)
    (lo : (stackPtr initial).toNat - 168 ≤ a.toNat)
    (hi : a.toNat < (stackPtr initial).toNat + 8)
    (apart : a.toNat < (stackPtr initial).toNat - 137 ∨
      (stackPtr initial).toNat - 120 ≤ a.toNat) :
    t.external[a]? = s.external[a]? := by
  have room : 1168 ≤ (stackPtr initial).toNat := hc.stackAvailable.2.2.1
  have rsp : (stackPtr s).toNat = (stackPtr initial).toNat - 176 := by
    rw [atCore.rsp]
    exact slot_toNat0 (k := 176) (by omega)
  have rdi : (s.regValue .rdi).toNat = (stackPtr initial).toNat - 137 := by
    rw [atCore.result]
    exact slot_toNat0 (k := 137) (by omega)
  have pair := hc.separation.1
  have wr : writtenRegions encrypt initial [key, nonce, aad, msg] =
      [bufferRegion encrypt initial, heapRegion encrypt initial, allocatorStateRegion,
        Stack.region initial 1168] := rfl
  rw [wr] at pair
  have heapStack := (List.pairwise_cons.mp pair.tail).1
    (Stack.region initial 1168) (by simp)
  rw [heap_region hc] at heapStack
  apply post.frame a
  intro r hr ar
  simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · simp only [resultRegion, registerRegion, resultBytes, MemoryRegion.Contains, rdi] at ar
    omega
  · apply heapStack a.toNat
    · change (initial.regValue .r8).toNat ≤ a.toNat ∧
        a.toNat < (initial.regValue .r8).toNat + (msg.size + 16)
      change (initial.regValue .r8).toNat ≤ a.toNat ∧
        a.toNat < (initial.regValue .r8).toNat + msg.size at ar
      constructor <;> omega
    · change (stackPtr initial).toNat - 1168 ≤ a.toNat ∧
        a.toNat < (stackPtr initial).toNat - 1168 +
          ((stackPtr initial).toNat + 8 - ((stackPtr initial).toNat - 1168))
      constructor <;> omega
  · change (stackPtr s).toNat - coreStackBytes ≤ a.toNat ∧
        a.toNat < (stackPtr s).toNat - coreStackBytes +
          ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - coreStackBytes)) at ar
    rw [rsp] at ar
    dsimp only [coreStackBytes] at ar
    omega

theorem core_word_kept [bindings : Bindings] {initial s t : RamState}
    {key : Vector UInt8 32} {nonce : Vector UInt8 12} {aad msg : ByteArray}
    (hc : ValidCall encrypt initial [key, nonce, aad, msg])
    (atCore : AtCore initial s msg.size)
    (post : CorePost s t key nonce aad msg (initial.regValue .r8))
    {k : Nat} (hk : k ≤ 168) (apart : k ≤ 120 ∨ 145 ≤ k) :
    wd t (stackPtr initial - BitVec.ofNat 64 k) =
      wd s (stackPtr initial - BitVec.ofNat 64 k) := by
  have st := entry_stack hc
  apply wd_congr
  intro i hi
  have ha := slot_toNat (I := stackPtr initial) (k := k) (i := i)
    (by have := st.room; omega) st.top (by omega)
  apply core_stack_kept hc atCore post
  · rw [ha]; have := st.room; omega
  · rw [ha]; have := st.room; omega
  · rw [ha]; have := st.room; omega

theorem core_result_zero [bindings : Bindings] {initial s t : RamState}
    {key : Vector UInt8 32} {nonce : Vector UInt8 12} {aad msg : ByteArray}
    (hc : ValidCall encrypt initial [key, nonce, aad, msg])
    (atCore : AtCore initial s msg.size)
    (post : CorePost s t key nonce aad msg (initial.regValue .r8)) :
    t.external[stackPtr initial - 137]? = some 0 := by
  have st := entry_stack hc
  have rdi : (s.regValue .rdi).toNat = (stackPtr initial).toNat - 137 := by
    rw [atCore.result]
    exact slot_toNat0 (k := 137) (by have := st.room; omega)
  have h := post.resultOk.2 ⟨0, by decide⟩
  simp only at h
  rw [rdi] at h
  have addr : BitVec.ofNat 64 ((stackPtr initial).toNat - 137 + 0) =
      stackPtr initial - 137 := by
    apply BitVec.eq_of_toNat_eq
    change ((stackPtr initial).toNat - 137 + 0) % 2^64 =
      (stackPtr initial - BitVec.ofNat 64 137).toNat
    rw [slot_toNat0 (I := stackPtr initial) (k := 137) (by have := st.room; omega)]
    have := st.top
    omega
  rw [addr] at h
  exact h

set_option maxRecDepth 8000 in
theorem core_return_word [bindings : Bindings] {initial s t : RamState}
    {key : Vector UInt8 32} {nonce : Vector UInt8 12} {aad msg : ByteArray}
    (hc : ValidCall encrypt initial [key, nonce, aad, msg])
    (atCore : AtCore initial s msg.size)
    (post : CorePost s t key nonce aad msg (initial.regValue .r8)) :
    wd t (stackPtr initial) = (returnBoundary initial).rip := by
  have st := entry_stack hc
  have word := core_word_kept hc atCore post (k := 0) (by omega) (by omega)
  change wd t (stackPtr initial - BitVec.ofNat 64 0) = wd s (stackPtr initial - BitVec.ofNat 64 0) at word
  simp only [BitVec.sub_zero] at word
  rw [word]
  change wd s (stackPtr initial) = wd initial (stackPtr initial)
  apply wd_congr
  intro i hi
  have ha : (stackPtr initial + BitVec.ofNat 64 i).toNat =
      (stackPtr initial).toNat + i := by
    have := st.top
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have inside : (Stack.region initial 1168).Contains
      (stackPtr initial + BitVec.ofNat 64 i).toNat := by
    have room : 1168 ≤ (stackPtr initial).toNat := hc.stackAvailable.2.2.1
    change (stackPtr initial).toNat - 1168 ≤ _ ∧
      _ < (stackPtr initial).toNat - 1168 +
        ((stackPtr initial).toNat + 8 - ((stackPtr initial).toNat - 1168))
    rw [ha]
    constructor <;> omega
  have pair := hc.separation.1
  have wr : writtenRegions encrypt initial [key, nonce, aad, msg] =
      [bufferRegion encrypt initial, heapRegion encrypt initial, allocatorStateRegion,
        Stack.region initial 1168] := rfl
  rw [wr] at pair
  apply atCore.frame
  intro r hr ar
  simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (List.pairwise_cons.mp pair.tail).1 _ (by simp) _ ar inside
  · exact (List.pairwise_cons.mp pair.tail.tail).1 _ (by simp) _ ar inside
  · change (stackPtr initial).toNat - 176 ≤
      (stackPtr initial + BitVec.ofNat 64 i).toNat ∧
      (stackPtr initial + BitVec.ofNat 64 i).toNat < (stackPtr initial).toNat - 176 + 176 at ar
    rw [ha] at ar
    have := st.room
    omega

theorem output_capacity {initial u : RamState}
    {key : Vector UInt8 32} {nonce : Vector UInt8 12} {aad msg : ByteArray}
    (hc : ValidCall encrypt initial [key, nonce, aad, msg])
    (frame : MemoryWriteFrame initial u
      #v[outputRegion encrypt initial, heapRegion encrypt initial, allocatorStateRegion,
        Stack.region initial encrypt.minStackBytes]) :
    ∃ cap, wd u (stackPtr initial + 32) = cap ∧ msg.size + 16 ≤ cap.toNat ∧
      (stackPtr initial).toNat + 40 < userAddressLimit := by
  obtain ⟨cap, arg, fit⟩ := hc.outputLengthArgumentCoversOutput rfl (.stack 3) rfl
  rw [output_region hc] at fit
  have argread := word64At_memLoad arg.2
  have addr : BitVec.ofNat 64 (stackArgumentSlot initial 3).start =
      stackPtr initial + 32 := by
    change BitVec.ofNat 64 ((stackPtr initial).toNat + 32) = _
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rfl
  rw [addr] at argread
  have ar : stackArgumentSlot initial 3 ∈ readRegions encrypt initial [key, nonce, aad, msg] := by
    simp [readRegions, encrypt, Routine.needsOutput, argumentRegions]
  have out : outputRegion encrypt initial = bufferRegion encrypt initial := by
    unfold outputRegion bufferRegion hasRoom bufferBytes
    simp [encrypt, Routine.inPlace]
  refine ⟨cap, ?_, fit, ?_⟩
  · change wd u (stackPtr initial + 32) = cap
    rw [← argread]
    apply wd_congr
    intro i hi
    apply frame
    intro r hr inside
    have written : r ∈ writtenRegions encrypt initial [key, nonce, aad, msg] := by
      simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [out] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp [writtenRegions, encrypt, Routine.needsOutput]
    apply hc.separation.2.1 r written _ ar _ inside
    have low := arg.1
    change (stackPtr initial).toNat + 32 ≤ _ ∧ _ < (stackPtr initial).toNat + 32 + 8
    change (stackPtr initial).toNat + 32 + 8 < userAddressLimit at low
    change (stackPtr initial).toNat + 32 ≤
      (stackPtr initial + BitVec.ofNat 64 32 + BitVec.ofNat 64 i).toNat ∧
      (stackPtr initial + BitVec.ofNat 64 32 + BitVec.ofNat 64 i).toNat <
        (stackPtr initial).toNat + 32 + 8
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    unfold userAddressLimit at low
    constructor <;> omega
  · exact arg.1

set_option maxRecDepth 8000 in
theorem core_frame [bindings : Bindings] {initial s t : RamState}
    {key : Vector UInt8 32} {nonce : Vector UInt8 12} {aad msg : ByteArray}
    (hc : ValidCall encrypt initial [key, nonce, aad, msg])
    (atCore : AtCore initial s msg.size)
    (post : CorePost s t key nonce aad msg (initial.regValue .r8)) :
    MemoryWriteFrame initial t
      #v[outputRegion encrypt initial, heapRegion encrypt initial, allocatorStateRegion,
        Stack.region initial encrypt.minStackBytes] := by
  have room : 1168 ≤ (stackPtr initial).toNat := hc.stackAvailable.2.2.1
  have st : Stack.region initial encrypt.minStackBytes =
      ⟨(stackPtr initial).toNat - 1168, 1176⟩ := stack_region_eq _ _ room
  have rsp : (stackPtr s).toNat = (stackPtr initial).toNat - 176 := by
    rw [atCore.rsp]
    exact slot_toNat0 (k := 176) (by omega)
  have rdi : (s.regValue .rdi).toNat = (stackPtr initial).toNat - 137 := by
    rw [atCore.result]
    exact slot_toNat0 (k := 137) (by omega)
  let regions := #v[outputRegion encrypt initial, heapRegion encrypt initial, allocatorStateRegion,
    Stack.region initial encrypt.minStackBytes]
  have f1 : MemoryWriteFrame initial s regions := frame_widen atCore.frame (by
    intro r hr x hx
    simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨heapRegion encrypt initial, by simp only [regions, Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], hx⟩
    · exact ⟨allocatorStateRegion, by simp only [regions, Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], hx⟩
    · refine ⟨Stack.region initial encrypt.minStackBytes, by simp only [regions, Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false, or_true], ?_⟩
      rw [st]
      change (stackPtr initial).toNat - 176 ≤ x ∧
        x < (stackPtr initial).toNat - 176 + 176 at hx
      change (stackPtr initial).toNat - 1168 ≤ x ∧
        x < (stackPtr initial).toNat - 1168 + 1176
      omega)
  have f2 : MemoryWriteFrame s t regions := frame_widen post.frame (by
    intro r hr x hx
    simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · refine ⟨Stack.region initial encrypt.minStackBytes, by simp only [regions, Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false, or_true], ?_⟩
      rw [st]
      simp only [resultRegion, resultBytes, registerRegion, MemoryRegion.Contains, rdi] at hx ⊢
      omega
    · refine ⟨heapRegion encrypt initial, by simp only [regions, Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], ?_⟩
      rw [heap_region hc]
      simp only [messageRegion, registerRegion, MemoryRegion.Contains] at hx ⊢
      omega
    · refine ⟨Stack.region initial encrypt.minStackBytes, by simp only [regions, Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false, or_true], ?_⟩
      rw [st]
      change (stackPtr s).toNat - coreStackBytes ≤ x ∧
        x < (stackPtr s).toNat - coreStackBytes +
          ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - coreStackBytes)) at hx
      rw [rsp] at hx
      simp only [coreStackBytes, MemoryRegion.Contains] at hx ⊢
      omega)
  exact memoryWriteFrame_trans f1 f2

theorem outside_memcpy {pc : BitVec 64} (outside : ¬ InProgram pc) :
    pc.toNat < 0x102dc0 ∨ 0x102def ≤ pc.toNat := by
  by_cases h : pc.toNat < 0x102dc0
  · exact .inl h
  · right
    apply Classical.byContradiction
    intro hn
    apply outside
    have hp := code_inProgram 0x2dc0 47 (by decide +kernel)
      (pc.toNat - 0x102dc0) (by omega)
    have eq : (0x102dc0 : BitVec 64) + BitVec.ofNat 64 (pc.toNat - 0x102dc0) = pc := by
      apply BitVec.eq_of_toNat_eq
      have c : (0x102dc0 : BitVec 64).toNat = 0x102dc0 := rfl
      rw [BitVec.toNat_add, c, BitVec.toNat_ofNat]
      omega
    change InProgram ((0x102dc0 : BitVec 64) + BitVec.ofNat 64 (pc.toNat - 0x102dc0)) at hp
    rwa [eq] at hp

end ChaCha20Poly1305.Proofs.Encrypt.Suffix
