import P256.Proofs.Nonce.Interface
import X86Proofs.Program.ReadWrite.Bytes

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Seed

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem replicate32_of_words {s : RamState} {address : BitVec 64}
    (word : BitVec 64) (byte : UInt8)
    (encoded : ∀ i < 8, storedByte word i = byte)
    (allocated : ∀ i < 32, (s.external[address + BitVec.ofNat 64 i]?).isSome)
    (words : ∀ j < 4, memLoad s.external (address + BitVec.ofNat 64 (8*j)) 64 = word) :
    ({ start := address.toNat, size := 32 } : MemoryRegion).HasBytes s.external
      ⟨Array.replicate 32 byte⟩ := by
  refine ⟨rfl, ?_⟩
  intro i
  have bound : i.val < 32 := i.isLt
  have bytes := Bytes.of_memLoad (n := 64)
    (a := address + BitVec.ofNat 64 (8 * (i.val / 8)))
    (m := s.external) (by
      intro j hj
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact allocated _ (by omega))
  rw [words (i.val/8) (by omega)] at bytes
  have result := bytes (i.val % 8) (by omega)
  rw [BitVec.add_assoc, ← BitVec.ofNat_add,
    show 8 * (i.val / 8) + i.val % 8 = i.val by omega,
    encoded _ (by omega)] at result
  simpa only [ByteArray.getElem_eq_getElem_data, Array.getElem_replicate,
    BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using result

end P256.Proofs.Nonce.Initialize.Seed
