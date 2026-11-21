import P256.Proofs.Signing.Wrapper.Hash.Finalize.Compress.Blocks.Correct
import P256.Proofs.Signing.Wrapper.Hash.Finalize.Compress.Control
import P256.Proofs.HMAC.Finalize.Padding.Bytes

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash.Finalize

open P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Compress

theorem compress [Bindings] {initial start s : RamState} {secret message : ByteArray}
    (pre : HashEntry initial start secret message)
    (input : Padded initial start s message) : ∃ t, Compressed initial start t message := by
  obtain ⟨a, branched, ripA, bytesA⟩ := Compress.branch pre input
  let firstHash := if message.size % 64 < 56 then SHA256.compressBlocks SHA256.initialHash message
    else SHA256.Reference.compress (SHA256.compressBlocks SHA256.initialHash message)
      (Standards.NIST.SHA2.bytesToBits (SHA256.paddedBuffer message))
  have ready : ∃ b, Working initial start b message firstHash ∧ b.RIP = 0x10293d ∧
      (MemoryRegion.mk (frameBase initial + 64).toNat 56).HasBytes b.external (SHA256.finalPrefix message) := by
    by_cases small : message.size % 64 < 56
    · refine ⟨a, ?_, ?_, ?_⟩
      · simpa only [firstHash, small, ite_true] using branched
      · simpa only [small, ite_true] using ripA
      · have prefixBytes := SHA256.hasBytes_prefix bytesA (count := 56) (by change 56 ≤ 64; decide)
        rw [SHA256.paddedBuffer_prefix message small] at prefixBytes
        exact prefixBytes
    · have start : a.RIP = 0x10289f := by simpa only [small, ite_false] using ripA
      obtain ⟨b, compressed, ripB⟩ := Compress.Blocks.first pre branched start bytesA
      obtain ⟨c, cleared, ripC, bytesC⟩ := Compress.Blocks.zero pre compressed ripB (by omega)
      exact ⟨c, by simpa only [firstHash, small, ite_false] using cleared, ripC, by
        simpa only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc,
          BitVec.reduceNeg, BitVec.reduceAdd] using bytesC⟩
  obtain ⟨b, working, ripB, prefixBytes⟩ := ready
  obtain ⟨c, lengthReady⟩ := Compress.length pre working ripB prefixBytes
  obtain ⟨t, output, ripT⟩ := Compress.Blocks.last pre lengthReady
  refine ⟨t, output.toLive, ripT, ⟨_, output.hashWords, ?_⟩⟩
  exact SHA256.serializeHash_finalize message

end P256.Proofs.Signing.Wrapper.Hash.Finalize
