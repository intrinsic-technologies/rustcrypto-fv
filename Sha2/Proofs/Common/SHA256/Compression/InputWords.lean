import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.SHA256.Compression.InputWords.Encoding
import Sha2.Proofs.Common.SHA256.Mathematics.Schedule
import Prelude.Memory.Region
import X86Proofs.Program.ReadWrite.Bytes

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression

open Sha2.Proofs.NIST Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem initialSchedule_getLsbD (bits : Array Bool) (i : Nat) (hi : i < 16)
    (hspan : 32 * (i + 1) ≤ bits.size) (k : Nat) (hk : k < 32) :
    ((initialSchedule bits)[i]!).toBitVec.getLsbD k = bits[32 * i + (31 - k)]! := by
  have hword : (initialSchedule bits)[i]! =
      UInt32.ofNat (Encoding.bitsToNat (bits.extract (32 * i) (32 * (i + 1)))) := by
    simp [initialSchedule, hi]
  have hsize : (bits.extract (32 * i) (32 * (i + 1))).size = 32 := by
    simp only [Array.size_extract]
    omega
  rw [hword, UInt32.toBitVec_ofNat', BitVec.getLsbD_ofNat,
    decide_eq_true hk, Bool.true_and,
    bitsToNat_testBit _ k (by rw [hsize]; exact hk), hsize]
  rw [getElem!_pos _ _ (by rw [hsize]; omega), Array.getElem_extract,
    getElem!_pos _ _ (by omega)]

theorem bswap32_memLoad_getLsbD (memory : Ram) (address : BitVec 64)
    (k : Nat) (hk : k < 32) :
    (bswap32 (memLoad memory address 32)).getLsbD k =
      (memByte memory (address + BitVec.ofNat 64 (3 - k / 8))).toBitVec.getLsbD (k % 8) := by
  have hb := bswap32_byte (memLoad memory address 32) (k / 8) (by omega)
  have hm := congrArg UInt8.toBitVec
    (storedByte_memLoad memory address (n := 32) (3 - k / 8) (by omega))
  rw [storedByte_eq_extract, UInt8.toBitVec_ofBitVec] at hm
  rw [hm] at hb
  have h := congrArg (fun v : BitVec 8 => v.getLsbD (k % 8)) hb
  simpa only [BitVec.getLsbD_extractLsb', show k % 8 < 8 by omega,
    decide_true, Bool.true_and, show 8 * (k / 8) + k % 8 = k by omega] using h

theorem bswap32_memLoad_initialSchedule {memory : Ram} {region : MemoryRegion}
    {block : ByteArray} (hbytes : region.HasBytes memory block)
    (i : Nat) (hi : i < 16) (hspan : 4 * (i + 1) ≤ block.size) :
    bswap32 (memLoad memory (BitVec.ofNat 64 region.start + BitVec.ofNat 64 (4 * i)) 32) =
      ((initialSchedule (Encoding.octetsToBits block))[i]!).toBitVec := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [bswap32_memLoad_getLsbD _ _ k hk,
    initialSchedule_getLsbD _ i hi (by rw [octetsToBits_size]; omega) k hk,
    octetsToBits_getElem! _ _ (by omega)]
  have hindex : (32 * i + (31 - k)) / 8 = 4 * i + (3 - k / 8) := by omega
  have hbit : 7 - (32 * i + (31 - k)) % 8 = k % 8 := by omega
  rw [hindex, hbit]
  have hbyteIndex : 4 * i + (3 - k / 8) < block.data.size := by
    change _ < block.size
    omega
  have hb := hbytes.2 ⟨4 * i + (3 - k / 8), by omega⟩
  change memory[BitVec.ofNat 64 (region.start + (4 * i + (3 - k / 8)))]? =
    some block.data[4 * i + (3 - k / 8)] at hb
  have ha : BitVec.ofNat 64 region.start + BitVec.ofNat 64 (4 * i) +
      BitVec.ofNat 64 (3 - k / 8) =
      BitVec.ofNat 64 (region.start + (4 * i + (3 - k / 8))) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
  simp only [memByte, PhysicalMemory.read, ha, hb, Option.getD_some]
  rw [getElem!_pos block.data _ (by change _ < block.size; omega)]
  rfl

theorem bswap32_memLoad_schedule {memory : Ram} {region : MemoryRegion}
    {block : ByteArray} (hbytes : region.HasBytes memory block)
    (hsize : region.size = 64) (i : Nat) (hi : i < 16) :
    bswap32 (memLoad memory (BitVec.ofNat 64 region.start + BitVec.ofNat 64 (4 * i)) 32) =
      ((schedule (Encoding.octetsToBits block))[i]!).toBitVec := by
  rw [schedule_getElem!_initial _ i hi]
  apply bswap32_memLoad_initialSchedule hbytes i hi
  have hs : block.size = 64 := hbytes.1.trans hsize
  omega

theorem input_memLoad_word {s : RamState} {address : BitVec 64} {block : ByteArray}
    (hbytes : (⟨address.toNat, 64⟩ : MemoryRegion).HasBytes s.external block)
    (i : Nat) (hi : i < 16) :
    bswap32 (memLoad s.external (address + BitVec.ofNat 64 (4 * i)) 32) =
      ((schedule (Encoding.octetsToBits block))[i]!).toBitVec := by
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
    bswap32_memLoad_schedule hbytes rfl i hi

end Sha2.Proofs.Common.SHA256.Compression
