import Sha2.Proofs.Common.SHA256.Compression.InputWords.Encoding
import Sha2.Proofs.Common.Instructions.Bswap
import Sha2.Proofs.Common.SHA512.Mathematics.Padding.Encoding
import Sha2.Proofs.Common.SHA512.Mathematics.Schedule
import Prelude.Memory.Region
import X86Proofs.Program.ReadWrite.Bytes

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression

open Sha2.Proofs.NIST Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

theorem initialSchedule_getLsbD (bits : Array Bool) (i : Nat) (hi : i < 16)
    (hspan : 64 * (i + 1) ≤ bits.size) (k : Nat) (hk : k < 64) :
    ((initialSchedule bits)[i]!).toBitVec.getLsbD k = bits[64 * i + (63 - k)]! := by
  have hword : (initialSchedule bits)[i]! =
      UInt64.ofNat (Encoding.bitsToNat (bits.extract (64 * i) (64 * (i + 1)))) := by
    simp [initialSchedule, hi]
  have hsize : (bits.extract (64 * i) (64 * (i + 1))).size = 64 := by
    simp only [Array.size_extract]
    omega
  rw [hword, UInt64.toBitVec_ofNat', BitVec.getLsbD_ofNat,
    decide_eq_true hk, Bool.true_and,
    Sha2.Proofs.Common.SHA256.Compression.bitsToNat_testBit _ k (by rw [hsize]; exact hk), hsize]
  rw [getElem!_pos _ _ (by rw [hsize]; omega), Array.getElem_extract,
    getElem!_pos _ _ (by omega)]

theorem bswap64_memLoad_getLsbD (memory : Ram) (address : BitVec 64)
    (k : Nat) (hk : k < 64) :
    (bswap64 (memLoad memory address 64)).getLsbD k =
      (memByte memory (address + BitVec.ofNat 64 (7 - k / 8))).toBitVec.getLsbD (k % 8) := by
  have hb := bswap64_byte (memLoad memory address 64) (k / 8) (by omega)
  have hm := congrArg UInt8.toBitVec
    (storedByte_memLoad memory address (n := 64) (7 - k / 8) (by omega))
  rw [storedByte_eq_extract, UInt8.toBitVec_ofBitVec] at hm
  rw [hm] at hb
  have h := congrArg (fun v : BitVec 8 => v.getLsbD (k % 8)) hb
  simpa only [BitVec.getLsbD_extractLsb', show k % 8 < 8 by omega,
    decide_true, Bool.true_and, show 8 * (k / 8) + k % 8 = k by omega] using h

theorem bswap64_memLoad_initialSchedule {memory : Ram} {region : MemoryRegion}
    {block : ByteArray} (hbytes : region.HasBytes memory block)
    (i : Nat) (hi : i < 16) (hspan : 8 * (i + 1) ≤ block.size) :
    bswap64 (memLoad memory (BitVec.ofNat 64 region.start + BitVec.ofNat 64 (8 * i)) 64) =
      ((initialSchedule (Encoding.octetsToBits block))[i]!).toBitVec := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [bswap64_memLoad_getLsbD _ _ k hk,
    initialSchedule_getLsbD _ i hi (by rw [octetsToBits_size]; omega) k hk,
    octetsToBits_getElem! _ _ (by omega)]
  have hindex : (64 * i + (63 - k)) / 8 = 8 * i + (7 - k / 8) := by omega
  have hbit : 7 - (64 * i + (63 - k)) % 8 = k % 8 := by omega
  rw [hindex, hbit]
  have hbyteIndex : 8 * i + (7 - k / 8) < block.data.size := by
    change _ < block.size
    omega
  have hb := hbytes.2 ⟨8 * i + (7 - k / 8), by omega⟩
  change memory[BitVec.ofNat 64 (region.start + (8 * i + (7 - k / 8)))]? =
    some block.data[8 * i + (7 - k / 8)] at hb
  have ha : BitVec.ofNat 64 region.start + BitVec.ofNat 64 (8 * i) +
      BitVec.ofNat 64 (7 - k / 8) =
      BitVec.ofNat 64 (region.start + (8 * i + (7 - k / 8))) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
  simp only [memByte, PhysicalMemory.read, ha, hb, Option.getD_some]
  rw [getElem!_pos block.data _ (by change _ < block.size; omega)]
  rfl

theorem bswap64_memLoad_schedule {memory : Ram} {region : MemoryRegion}
    {block : ByteArray} (hbytes : region.HasBytes memory block)
    (hsize : region.size = 128) (i : Nat) (hi : i < 16) :
    bswap64 (memLoad memory (BitVec.ofNat 64 region.start + BitVec.ofNat 64 (8 * i)) 64) =
      ((schedule (Encoding.octetsToBits block))[i]!).toBitVec := by
  rw [schedule_getElem!_initial _ i hi]
  apply bswap64_memLoad_initialSchedule hbytes i hi
  have hs : block.size = 128 := hbytes.1.trans hsize
  omega

theorem input_memLoad_word {s : RamState} {address : BitVec 64} {block : ByteArray}
    (hbytes : (⟨address.toNat, 128⟩ : MemoryRegion).HasBytes s.external block)
    (i : Nat) (hi : i < 16) :
    bswap64 (memLoad s.external (address + BitVec.ofNat 64 (8 * i)) 64) =
      ((schedule (Encoding.octetsToBits block))[i]!).toBitVec := by
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
    bswap64_memLoad_schedule hbytes rfl i hi

end Sha2.Proofs.Common.SHA512.Compression
