import AesGcm.Proofs.Machine.CTR.GCTR
import AesGcm.Proofs.Machine.Runtime.MemorySlices
import AesGcm.Proofs.Machine.Runtime.Preservation

namespace AesGcm.Proofs.Machine.Core.Decrypt

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime Standards.NIST.GCM AesGcm.Spec.GCM

theorem tail_output {fr : Activation} {before after : Ram} {dst : BitVec 64}
    {cipher : Vector Bool 128 → Vector Bool 128} {counter : Vector Bool 128}
    {front tail : ByteArray} {blocks : Nat} (count : front.size = 16 * blocks)
    (bound : dst.toNat + front.size < 2^64)
    (sep : (callStack fr).Disjoint (span dst front.size))
    (headBytes : (span dst front.size).HasBytes before
      (byteArrayOfBits (GCTR cipher counter (bitsOfByteArray front))))
    (frame : RamWriteFrame before after
      [fr.region, span (dst + BitVec.ofNat 64 front.size) tail.size])
    (suffix : (span (dst + BitVec.ofNat 64 front.size) tail.size).HasBytes after
      (byteArrayOfBits (GCTR cipher (Nat.repeat (inc 32) blocks counter) (bitsOfByteArray tail)))) :
    (span dst (front ++ tail).size).HasBytes after
      (byteArrayOfBits (GCTR cipher counter (bitsOfByteArray (front ++ tail)))) := by
  have start : (dst + BitVec.ofNat 64 front.size).toNat = dst.toNat + front.size := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : front.size < 2^64), Nat.mod_eq_of_lt bound]
  have prefixAfter := hasBytes_of_frame frame headBytes (Nat.le_of_lt bound) (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact span_disjoint_activationRegion sep
    · intro a ha hb
      change _ ∧ a < dst.toNat + front.size at ha
      change (dst + BitVec.ofNat 64 front.size).toNat ≤ a ∧ _ at hb
      omega)
  let first := byteArrayOfBits (GCTR cipher counter (bitsOfByteArray front))
  let rest := byteArrayOfBits (GCTR cipher (Nat.repeat (inc 32) blocks counter) (bitsOfByteArray tail))
  have firstSize : first.size = front.size := AesGcm.Proofs.byteArrayOfBits_size _
  have restSize : rest.size = tail.size := AesGcm.Proofs.byteArrayOfBits_size _
  rw [CTR.gctr_bytes_append_blocks cipher counter front tail blocks count, ByteArray.size_append]
  exact (show (span dst (front.size + tail.size)).HasBytes after (first ++ rest) by
    simpa only [firstSize, restSize] using hasBytes_append (front := first) (tail := rest)
      (by simpa only [firstSize] using prefixAfter) (by simpa only [firstSize, restSize] using suffix)
      (by rw [firstSize]; exact bound))

end AesGcm.Proofs.Machine.Core.Decrypt
