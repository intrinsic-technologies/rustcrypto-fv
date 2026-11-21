import P256.Proofs.HMAC.Finalize.OuterBuffer.Digest
import P256.Proofs.HMAC.Finalize.Copy

open P256.Proofs.Program
open P256.Proofs.Program.ScalarFrame (workRegion)

set_option autoImplicit false

namespace P256.Proofs.HMAC.Finalize.OuterBuffer

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem state_append_digest {s t : RamState} {a : BitVec 64} {key digest : ByteArray}
    (outer : Sha256StateAt s a (keyPad key 0x5c)) (size : digest.size = 32)
    (buffer : (MemoryRegion.mk a.toNat 32).HasBytes t.external digest)
    (position : t.external[a + 63]? = some 32)
    (preserved : ∀ i < 40, t.external[a + 64 + BitVec.ofNat 64 i]? =
      s.external[a + 64 + BitVec.ofNat 64 i]?) :
    Sha256StateAt t a (keyPad key 0x5c ++ digest) := by
  apply sha256StateAt_keyPad_append
  · simpa only [size, Nat.reduceMod, remainderBytes_short digest (by omega)] using buffer
  · simpa only [size, Nat.reduceMod, UInt8.reduceOfNat] using position
  · rw [compressBlocks_short _ digest (by omega)]
    have hash := outer.hash.copy (fun i hi => preserved i (by omega))
    simpa only [compressBlocks_keyPad] using hash
  · have copied := copied_sub (offset := 32) (len := 8) preserved (by decide)
    have addr : a + 64 + 32#64 = a + 96 := by rw [BitVec.add_assoc]; rfl
    rw [addr] at copied
    have result := loadBytes_ok_copy copied outer.count
    simpa only [keyPad_size, size, Nat.reduceDiv, Nat.add_zero] using result

end P256.Proofs.HMAC.Finalize.OuterBuffer
