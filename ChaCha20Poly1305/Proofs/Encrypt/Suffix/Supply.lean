import ChaCha20Poly1305.Proofs.Encrypt.Suffix.Facts
import ChaCha20Poly1305.Proofs.MemoryContracts

namespace ChaCha20Poly1305.Proofs.Encrypt.Suffix

open ChaCha20Poly1305.Spec ChaCha20Poly1305.Spec.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Wrapper MemoryRoutines.Machine

theorem memcpy_pre {initial u : RamState}
    {key : Vector UInt8 32} {nonce : Vector UInt8 12} {aad msg : ByteArray}
    (hc : ValidCall encrypt initial [key, nonce, aad, msg])
    (grows : Grows initial u) (df : DirectionFlagUnset u)
    (rip : u.RIP = 0x102dc0) (rsp : stackPtr u = stackPtr initial - 176)
    (dst : rd u 7 = initial.regValue .r9) (src : rd u 6 = initial.regValue .r8)
    (len : rd u 2 = BitVec.ofNat 64 (msg.size + 16))
    (ret : (returnBoundary u).rip = 0x1018be) : MemoryContracts.MemcpyPre u := by
  have st := entry_stack hc
  have heap := (hc.heapInMemory rfl).1
  rw [heap_region hc] at heap
  have out := hc.outputInMemory rfl
  have buf : bufferRegion encrypt initial = registerRegion initial .r9 (msg.size + 16) := by
    change registerRegion initial .r9 (messageBytes encrypt initial + 16) = _
    rw [message_length hc]
  rw [buf] at out
  have hb : (initial.regValue .r8).toNat + (msg.size + 16) < userAddressLimit := heap.1
  have ob : (initial.regValue .r9).toNat + (msg.size + 16) < userAddressLimit := out.1
  have length : (MemoryContracts.rdx.read u).toNat = msg.size + 16 := by
    change (rd u 2).toNat = _
    rw [len, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold userAddressLimit at hb; omega)]
  have di : rdi.read u = initial.regValue .r9 := dst
  have si : rsi.read u = initial.regValue .r8 := src
  have writable : Common.WritableRange u (initial.regValue .r9) (msg.size + 16) := by
    have av := hc.separation.2.2 (bufferRegion encrypt initial)
      (by simp [writtenRegions, encrypt, Routine.needsOutput])
    rw [buf] at av
    have inside : ∀ i < msg.size + 16, (registerRegion initial .r9 (msg.size + 16)).Contains
        (initial.regValue .r9 + BitVec.ofNat 64 i).toNat := by
      intro i hi
      change (initial.regValue .r9).toNat ≤ _ ∧ _ < (initial.regValue .r9).toNat + (msg.size + 16)
      rw [toNat_add_ofNat _ _ (by unfold userAddressLimit at ob; omega)]
      omega
    refine ⟨⟨Nat.le_of_lt ob, ?_⟩, ?_, ?_⟩
    · intro i hi
      exact grows _ (Option.isSome_iff_exists.mpr (out.2 _ (inside i hi)))
    · intro i hi h
      exact av _ (inside i hi) (.inr h)
    · intro i hi h
      exact av _ (inside i hi) (.inl h)
  have source : MemReadable u (initial.regValue .r8) (msg.size + 16) := by
    refine ⟨Nat.le_of_lt hb, ?_⟩
    intro i hi
    apply grows
    apply Option.isSome_iff_exists.mpr
    apply heap.2
    change (initial.regValue .r8).toNat ≤ _ ∧ _ < (initial.regValue .r8).toNat + (msg.size + 16)
    rw [toNat_add_ofNat _ _ (by unfold userAddressLimit at hb; omega)]
    omega
  have pair := hc.separation.1
  have wr : writtenRegions encrypt initial [key, nonce, aad, msg] =
      [bufferRegion encrypt initial, heapRegion encrypt initial, allocatorStateRegion,
        Stack.region initial 1168] := rfl
  rw [wr] at pair
  have oh := (List.pairwise_cons.mp pair).1 (heapRegion encrypt initial) (by simp)
  have os := (List.pairwise_cons.mp pair).1 (Stack.region initial 1168) (by simp)
  rw [buf, heap_region hc] at oh
  rw [buf] at os
  have room : 1168 ≤ (stackPtr initial).toNat := hc.stackAvailable.2.2.1
  have stEq := stack_region_eq initial 1168 room
  have ohEnds := region_sep oh (by change 0 < msg.size + 16; omega) (by change 0 < msg.size + 16; omega)
  have osEnds := region_sep os (by change 0 < msg.size + 16; omega) (by rw [stEq]; exact Nat.zero_lt_succ _)
  rw [stEq] at osEnds
  have rspNat : (stackPtr u).toNat = (stackPtr initial).toNat - 176 := by
    rw [rsp]
    exact slot_toNat0 (I := stackPtr initial) (k := 176) (by omega)
  refine ⟨⟨rip, df.df, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [di, length]; exact writable
  · rw [rsp]
    change MemReadable u (stackPtr initial - BitVec.ofNat 64 176) 8
    refine ⟨by rw [slot_toNat0 (k := 176) (by omega)]; have := st.top; omega, ?_⟩
    intro i hi
    apply grows
    apply st.allocated <;> rw [slot_toNat (k := 176) (by omega) st.top (by omega)] <;> omega
  · rw [di, length]
    apply RangeApart.of_toNat
    · unfold userAddressLimit at ob; omega
    · rw [rspNat]; have := st.top; omega
    · rw [rspNat]
      change (initial.regValue .r9).toNat + (msg.size + 16) ≤ _ ∨
        _ ≤ (initial.regValue .r9).toNat
      change (initial.regValue .r9).toNat + (msg.size + 16) ≤ (stackPtr initial).toNat - 1168 ∨
        (stackPtr initial).toNat - 1168 + 1176 ≤ (initial.regValue .r9).toNat at osEnds
      omega
  · rw [ret]; decide
  · rw [ret]; decide
  · rw [si, length]; exact source
  · rw [si, di, length]
    exact ohEnds.symm

end ChaCha20Poly1305.Proofs.Encrypt.Suffix
