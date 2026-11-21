import P256.Proofs.Nonce.Update.Absorb.Mathematics
import P256.Proofs.HMAC.Finalize.Copy

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Absorb

open P256.Spec P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem hmacStateAt_append_small {s t : RamState} {a : BitVec 64}
    {key input added : ByteArray} (initial : HMAC.HmacStateAt s a key input)
    (fits : input.size % 64 + added.size < 64)
    (buffer : (MemoryRegion.mk (a + 64).toNat (input.size % 64 + added.size)).HasBytes
      t.external (SHA256.remainderBytes input ++ added))
    (position : t.external[a + 127]? = some (UInt8.ofNat (input.size % 64 + added.size)))
    (preserved : ∀ i < 168, i < 64 ∨ 128 ≤ i →
      t.external[a + BitVec.ofNat 64 i]? = s.external[a + BitVec.ofNat 64 i]?) :
    HMAC.HmacStateAt t a key (input ++ added) := by
  have modulo : (input ++ added).size % 64 = input.size % 64 + added.size := by
    rw [ByteArray.size_append]
    omega
  have quotient : (input ++ added).size / 64 = input.size / 64 := by
    rw [ByteArray.size_append]
    omega
  refine ⟨hasBytes_copy initial.outer (fun i hi => preserved i (by omega) (.inl hi)), ?_⟩
  apply HMAC.sha256StateAt_keyPad_append
  · simpa only [modulo, remainderBytes_append_small _ _ fits] using buffer
  · simpa only [modulo, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using position
  · rw [compressBlocks_append_small _ _ _ fits]
    apply SHA256.HashStateAt.copy (by
      simpa only [HMAC.compressBlocks_keyPad_append] using initial.inner.hash)
    intro i hi
    have h := preserved (128 + i) (by omega) (.inr (by omega))
    simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using h
  · rw [quotient]
    have oldCount : loadBytes s.external (a + 64 + 96) 8 = .ok (BitVec.ofNat 64 (1 + input.size / 64)) := by
      have h := initial.inner.count
      rw [ByteArray.size_append, HMAC.keyPad_size] at h
      rwa [show (64 + input.size) / 64 = 1 + input.size / 64 by omega] at h
    apply loadBytes_ok_copy (a := a + 64 + 96) _ oldCount
    intro i hi
    have h := preserved (160 + i) (by omega) (.inr (by omega))
    simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using h

end P256.Proofs.Nonce.Update.Absorb
