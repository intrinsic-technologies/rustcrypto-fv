import ChaCha20Poly1305.Proofs.Encrypt.Prefix.Allocate.Environment
import ChaCha20Poly1305.Proofs.MemoryContracts

namespace ChaCha20Poly1305.Proofs.Encrypt.Prefix

open ChaCha20Poly1305.Spec ChaCha20Poly1305.Spec.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs Wrapper

theorem copy_pre [Bindings] {initial s : RamState} {key : Vector UInt8 32} {nonce : Vector UInt8 12}
    {aad msg : ByteArray} (hc : ValidCall encrypt initial [key, nonce, aad, msg])
    (hs : Common initial s key) (st : EntryStack initial) (pos : 0 < msg.size)
    (rip : s.RIP = 0x102dc0) (rsp : stackPtr s = stackPtr initial - BitVec.ofNat 64 176)
    (ret : (returnBoundary s).rip = 0x101828)
    (dst : rdi.read s = initial.regValue .r8) (src : rsi.read s = initial.regValue .rcx)
    (len : MemoryContracts.rdx.read s = BitVec.ofNat 64 msg.size) :
    MemoryContracts.MemcpyPre s := by
  have hd := heap_writable hc hs.grows
  have hlow : (initial.regValue .r8).toNat + msg.size ≤ 2^32 := hd.readable.low
  have hn : (MemoryContracts.rdx.read s).toNat = msg.size := by
    rw [len, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsrc := original_input hc hs.frame
    (r := registerRegion initial .rcx msg.size) (by simp [readRegions, encrypt, inputRegion])
    hc.inputsInMemory.2.2.2.1
  have hstack := heap_stack_disjoint hc
  have room := st.room
  refine ⟨⟨rip, hs.direction.df, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [dst, hn]; exact hd
  · rw [rsp]
    have hr := slot_writable st hs.grows (k := 176) (by omega) (by omega)
    exact ⟨hr.low, hr.mem⟩
  · rw [dst, hn, rsp]
    intro i hi j hj eq
    apply hstack (initial.regValue .r8 + BitVec.ofNat 64 i).toNat
    · rw [heap_region hc]
      change (initial.regValue .r8).toNat ≤ _ ∧ _ < (initial.regValue .r8).toNat + (msg.size + 16)
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    · rw [eq, slot_toNat (by omega) st.top (by omega)]
      change (stackPtr initial).toNat - 1168 ≤ _ ∧ _ <
        (stackPtr initial).toNat - 1168 +
          ((stackPtr initial).toNat + 8 - ((stackPtr initial).toNat - 1168))
      omega
  · rw [ret]; decide
  · rw [ret]; left; decide
  · rw [src, hn]
    exact input_readable hsrc
  · rw [src, dst, hn]
    exact input_heap_disjoint hc pos

end ChaCha20Poly1305.Proofs.Encrypt.Prefix
