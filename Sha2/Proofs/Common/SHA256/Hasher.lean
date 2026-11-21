import Sha2.Proofs.Wrapper.Memory
import Sha2.Proofs.Common.SHA256.Mathematics.Padding.Tail

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure HasherAt (s : RamState) (base : BitVec 64) (message : ByteArray)
    (initialHash : Array UInt32 := NIST.SHA256.initialHash) : Prop where
  hashWords : HashStateAt s (base + 64) (compressBlocks initialHash message)
  tailBytes : (⟨base.toNat, message.size % 64⟩ : MemoryRegion).HasBytes
    s.external (remainderBytes message)
  tailLength : s.external[base + 63]? = some (UInt8.ofNat (message.size % 64))
  blocks : memLoad s.external (base + 96) 64 = BitVec.ofNat 64 (message.size / 64)

theorem HasherAt.of_bytes {s t : RamState} {source destination : BitVec 64}
    {message : ByteArray} {initialHash : Array UInt32}
    (input : HasherAt s source message initialHash)
    (bytes : ∀ i < 104, t.external[destination + BitVec.ofNat 64 i]? =
      s.external[source + BitVec.ofNat 64 i]?) : HasherAt t destination message initialHash := by
  refine ⟨Sha2.Proofs.Wrapper.hashState_of_bytes input.hashWords ?_,
    ⟨input.tailBytes.1, ?_⟩, (bytes 63 (by decide)).trans input.tailLength, ?_⟩
  · intro i hi
    simpa only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat]
      using bytes (64 + i) (by omega)
  · intro i
    have hi := i.isLt
    have size := remainderBytes_size message
    have copied := bytes i.val (by omega)
    have original := input.tailBytes.2 i
    simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      using copied.trans (by simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat,
        BitVec.setWidth_eq] using original)
  · rw [← input.blocks]
    apply memLoad_congr
    intro i hi
    change (t.external[_]?).getD 0 = (s.external[_]?).getD 0
    have copied := bytes (96 + i) (by omega)
    simpa only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat]
      using congrArg (fun b => b.getD 0) copied

end Sha2.Proofs.Common.SHA256
