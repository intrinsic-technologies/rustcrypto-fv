import Hkdf.Proofs.Common.SHA256.Compression.Bswap32
import Hkdf.Proofs.Common.SHA256.Interfaces
import X86Proofs.Program.ReadWrite.Bytes
import Prelude.Memory.Region
import Init.Data.ByteArray.Lemmas

set_option autoImplicit false

namespace Hkdf.Proofs.Common.Memory

open Prelude X86 X86.Machine

theorem hasBytes_prefix {memory : Ram} {region : MemoryRegion} {bytes : ByteArray}
    {count : Nat} (input : region.HasBytes memory bytes) (bound : count ≤ region.size) :
    (⟨region.start, count⟩ : MemoryRegion).HasBytes memory (bytes.extract 0 count) := by
  have size : (bytes.extract 0 count).size = count := by
    rw [ByteArray.size_extract, Nat.sub_zero]
    have hsize : bytes.size = region.size := input.1
    omega
  refine ⟨size, ?_⟩
  intro i
  have hi : i.val < bytes.size := by
    have := i.isLt
    have hsize : bytes.size = region.size := input.1
    omega
  simpa only [ByteArray.getElem_extract, Nat.zero_add] using input.2 ⟨i.val, hi⟩

end Hkdf.Proofs.Common.Memory

namespace Hkdf.Proofs.Common.Memory

open Prelude X86 X86.Machine X86Proofs
open Hkdf.Proofs.Common.SHA256.Compression

 theorem bswap32_storedByte (word : UInt32) {i : Nat} (hi : i < 4) :
    storedByte (bswap32 word.toBitVec) i =
      UInt8.ofNat (word.toNat / 256 ^ (3 - i) % 256) := by
  rw [storedByte_eq_extract, bswap32_byte _ _ hi, ← storedByte_eq_extract]
  apply UInt8.toNat.inj
  simp only [storedByte, UInt8.toNat_ofNat', UInt32.toNat_toBitVec,
    Nat.shiftRight_eq_div_pow, Nat.mod_mod]
  rw [show 256 ^ (3 - i) = 2 ^ (8 * (3 - i)) by rw [Nat.pow_mul]]

 theorem bigEndian_bytes {s : RamState} {address : BitVec 64} {hash : Array UInt32}
    (allocated : ∀ i < 32, (s.external[address + BitVec.ofNat 64 i]?).isSome)
    (words : ∀ j < 8, memLoad s.external (address + BitVec.ofNat 64 (4 * j)) 32 =
      bswap32 hash[j]!.toBitVec) :
    Bytes s.external address 32
      (fun i => UInt8.ofNat (hash[i / 4]!.toNat / 256 ^ (3 - i % 4) % 256)) := by
  intro i hi
  have bytes := Bytes.of_memLoad (n := 32)
    (a := address + BitVec.ofNat 64 (4 * (i / 4)))
    (m := s.external) (by
      intro j hj
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact allocated _ (by omega))
  rw [words (i / 4) (by omega)] at bytes
  have byte := bytes (i % 4) (by omega)
  rw [BitVec.add_assoc, ← BitVec.ofNat_add,
    show 4 * (i / 4) + i % 4 = i by omega,
    bswap32_storedByte _ (by omega)] at byte
  exact byte

end Hkdf.Proofs.Common.Memory
