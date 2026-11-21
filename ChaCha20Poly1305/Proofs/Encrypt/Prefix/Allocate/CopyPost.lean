import ChaCha20Poly1305.Proofs.Encrypt.Prefix.Allocate.CopyPre
import ChaCha20Poly1305.Proofs.Encrypt.Prefix.Allocate.Copy

namespace ChaCha20Poly1305.Proofs.Encrypt.Prefix

open ChaCha20Poly1305.Spec ChaCha20Poly1305.Spec.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs Wrapper CoreContract

theorem copy_stack_eq [Bindings] {initial s t : RamState} {key : Vector UInt8 32}
    {nonce : Vector UInt8 12} {aad msg : ByteArray}
    (hc : ValidCall encrypt initial [key, nonce, aad, msg])
    (post : MemoryContracts.MemcpyResult s t)
    (dst : rdi.read s = initial.regValue .r8)
    (len : (MemoryContracts.rdx.read s).toNat = msg.size)
    (a : BitVec 64) (ha : (Stack.region initial 1168).Contains a.toNat) :
    t.external[a]? = s.external[a]? := by
  have low := (hc.heapInMemory rfl).1.1
  rw [heap_region hc] at low
  have low : (initial.regValue .r8).toNat + (msg.size + 16) < 2^32 := low
  apply post.toCallResult.frame (by rw [dst, len]; omega) a
  intro r hr ar
  have er : r = MemoryContracts.destination s := by simpa using hr
  subst r
  change (rdi.read s).toNat ≤ a.toNat ∧ a.toNat < (rdi.read s).toNat +
    (MemoryContracts.rdx.read s).toNat at ar
  rw [dst, len] at ar
  apply heap_stack_disjoint hc a.toNat ?_ ha
  rw [heap_region hc]
  change (initial.regValue .r8).toNat ≤ a.toNat ∧ a.toNat < (initial.regValue .r8).toNat + (msg.size + 16)
  omega

theorem Common.copy_step [Bindings] {initial s t : RamState} {key : Vector UInt8 32}
    {nonce : Vector UInt8 12} {aad msg : ByteArray}
    (hc : ValidCall encrypt initial [key, nonce, aad, msg]) (hs : Common initial s key)
    (st : EntryStack initial) (post : MemoryContracts.MemcpyResult s t)
    (dst : rdi.read s = initial.regValue .r8)
    (len : (MemoryContracts.rdx.read s).toNat = msg.size) : Common initial t key := by
  have hd := heap_writable hc hs.grows
  have hd' : ChaCha20Poly1305.Proofs.Common.WritableRange s (rdi.read s)
      (MemoryContracts.rdx.read s).toNat := by rw [dst, len]; exact hd
  have room := st.room
  apply hs.step (by omega) st.top post.agrees (by simp [MemoryRoutines.callChanges])
    post.ready (post.toCallResult.codeIn hd' hs.code)
  · intro a ha
    apply post.toCallResult.frame hd'.readable.low a
    intro r hr ar
    have er : r = MemoryContracts.destination s := by simpa using hr
    subst r
    apply ha (heapRegion encrypt initial) (by simp)
    rw [heap_region hc]
    change (rdi.read s).toNat ≤ a.toNat ∧ a.toNat < (rdi.read s).toNat +
      (MemoryContracts.rdx.read s).toNat at ar
    rw [dst, len] at ar
    change (initial.regValue .r8).toNat ≤ a.toNat ∧ a.toNat <
      (initial.regValue .r8).toNat + (msg.size + 16)
    omega
  · intro a lo hi
    apply copy_stack_eq hc post dst len a
    change (stackPtr initial).toNat - 1168 ≤ a.toNat ∧ a.toNat <
      (stackPtr initial).toNat - 1168 +
        ((stackPtr initial).toNat + 8 - ((stackPtr initial).toNat - 1168))
    have hr : 1168 ≤ (stackPtr initial).toNat := hc.stackAvailable.2.2.1
    omega

end ChaCha20Poly1305.Proofs.Encrypt.Prefix
