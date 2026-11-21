import P256.Proofs.HMAC.State
import P256.Proofs.HMAC.Key.Output.Bytes

set_option autoImplicit false

namespace P256.Proofs.Nonce.UpdateValue.Absorb

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem hmacStateAt_absorb_short {s t : RamState} {a : BitVec 64}
    {key input : ByteArray} (initial : HMAC.HmacStateAt s a key ByteArray.empty)
    (short : input.size < 64)
    (buffer : (MemoryRegion.mk (a + 64).toNat input.size).HasBytes t.external input)
    (position : t.external[a + 127]? = some (UInt8.ofNat input.size))
    (preserved : ∀ i < 168, i < 64 ∨ 128 ≤ i →
      t.external[a + BitVec.ofNat 64 i]? = s.external[a + BitVec.ofNat 64 i]?) :
    HMAC.HmacStateAt t a key input := by
  refine ⟨hasBytes_copy initial.outer (fun i hi => preserved i (by omega) (.inl hi)), ?_⟩
  apply HMAC.sha256StateAt_keyPad_append
  · simpa only [Nat.mod_eq_of_lt short, HMAC.remainderBytes_short input short] using buffer
  · simp only [Nat.mod_eq_of_lt short, BitVec.add_assoc, BitVec.reduceAdd]
    exact position
  · have hash : SHA256.HashStateAt s (a + 64 + 64)
        (P256.Proofs.SHA256.Reference.compress P256.Proofs.SHA256.initialHash
          (Standards.NIST.SHA2.bytesToBits (HMAC.keyPad key 0x36))) := by
      simpa only [ByteArray.append_empty, HMAC.compressBlocks_keyPad] using initial.inner.hash
    rw [HMAC.compressBlocks_short _ _ short]
    refine ⟨hash.1, ?_⟩
    intro j hj
    apply loadBytes_ok_copy (loaded := hash.2 j hj)
    intro i hi
    have h := preserved (128 + 4*j + i) (by omega) (.inr (by omega))
    simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using h
  · have count : loadBytes s.external (a + 64 + 96) 8 = .ok (BitVec.ofNat 64 1) := by
      simpa only [ByteArray.size_append, HMAC.keyPad_size, ByteArray.size_empty,
        Nat.add_zero, Nat.reduceDiv] using initial.inner.count
    rw [Nat.div_eq_of_lt short, Nat.add_zero]
    apply loadBytes_ok_copy (a := a + 64 + 96) _ count
    intro i hi
    have h := preserved (160 + i) (by omega) (.inr (by omega))
    simp only [BitVec.ofNat_add] at h
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using h

end P256.Proofs.Nonce.UpdateValue.Absorb
