import Sha2.Proofs.Common.SHA256.Absorb.State

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem hasher_append_short {s : RamState} {base : BitVec 64} {initialHash : Array UInt32} {prior bytes : ByteArray}
    (small : bytes.size < 64 - prior.size % 64)
    (hashWords : HashStateAt s (base + 64) (compressBlocks initialHash prior))
    (tailBytes : (⟨base.toNat, (remainderBytes prior ++ bytes).size⟩ : MemoryRegion).HasBytes
      s.external (remainderBytes prior ++ bytes))
    (tailLength : s.external[base + 63]? = some (UInt8.ofNat (prior.size % 64 + bytes.size)))
    (blocks : memLoad s.external (base + 96) 64 = BitVec.ofNat 64 (prior.size / 64)) :
    HasherAt s base (prior ++ bytes) initialHash := by
  have counts := Sha2.Proofs.Wrapper.Absorb.append_short_counts prior bytes small
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Sha2.Proofs.Wrapper.Absorb.compressBlocks_append_short _ _ _ small]
    exact hashWords
  · rw [Sha2.Proofs.Wrapper.Absorb.remainderBytes_append_short _ _ small, counts.2]
    simpa only [ByteArray.size_append, remainderBytes_size] using tailBytes
  · rw [counts.2]
    exact tailLength
  · rw [counts.1]
    exact blocks

theorem hasher_append_aligned {s : RamState} {base : BitVec 64}
    {initialHash : Array UInt32} {prior bytes : ByteArray} {consumed : Nat}
    (bound : consumed ≤ bytes.size)
    (aligned : (prior ++ bytes.extract 0 consumed).size % 64 = 0)
    (hashWords : HashStateAt s (base + 64)
      (compressBlocks (compressBlocks initialHash (prior ++ bytes.extract 0 consumed))
        (bytes.extract consumed (consumed + 64 * ((bytes.size - consumed) / 64)))))
    (tailBytes : (⟨base.toNat, (bytes.size - consumed) % 64⟩ : MemoryRegion).HasBytes s.external
      (bytes.extract (consumed + 64 * ((bytes.size - consumed) / 64)) bytes.size))
    (tailLength : s.external[base + 63]? = some (UInt8.ofNat ((bytes.size - consumed) % 64)))
    (blocks : memLoad s.external (base + 96) 64 =
      BitVec.ofNat 64 ((prior ++ bytes.extract 0 consumed).size / 64 + (bytes.size - consumed) / 64)) :
    HasherAt s base (prior ++ bytes) initialHash := by
  have counts := Sha2.Proofs.Wrapper.Absorb.Blocks.finish_counts prior bytes bound aligned
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Sha2.Proofs.Wrapper.Absorb.Blocks.finish_hash _ _ _ bound aligned] at hashWords
    exact hashWords
  · rw [Sha2.Proofs.Wrapper.Absorb.Blocks.finish_tail _ _ bound aligned, counts.2]
    exact tailBytes
  · rw [counts.2]
    exact tailLength
  · rw [counts.1]
    exact blocks

end Sha2.Proofs.Common.SHA256.Absorb
