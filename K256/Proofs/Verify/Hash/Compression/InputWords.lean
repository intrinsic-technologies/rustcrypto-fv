import K256.Proofs.Verify.Hash.Compression.Values
import K256.Proofs.Verify.Hash.Compression.Mathematics.Schedule
import K256.Proofs.Verify.Hash.Padding.Encoding
import Prelude.Memory.Region
import X86Proofs.Program.ReadWrite.Bytes

set_option autoImplicit false

namespace K256.Proofs.Verify.Hash.Compression

open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem bitsToNat_testBit (bits : Array Bool) (i : Nat) (hi : i < bits.size) :
    (Reference.bitsToNat bits).testBit i = bits[bits.size - 1 - i]! := by
  change (BitVec.ofBoolListBE bits.toList).getLsbD i = _
  rw [BitVec.getLsbD_ofBoolListBE]
  simp [hi, List.getD, getElem!_pos,
    show bits.size - 1 - i < bits.size by omega]

theorem bswap32_byte (x : BitVec 32) (i : Nat) (hi : i < 4) :
    (bswap32 x).extractLsb' (8*i) 8 = x.extractLsb' (8*(3-i)) 8 := by
  simpa only [bswap32, bswapSpec, lane, show (32 / 8 - 1 : Nat) = 3 by decide, Nat.mul_comm]
    using (lane_ofLanes (n := 32) (w := 8) (fun j => lane 8 x (3 - j)) i hi)

theorem initialSchedule_getLsbD (bits : Array Bool) (i : Nat) (hi : i < 16)
    (hspan : 32 * (i + 1) ≤ bits.size) (k : Nat) (hk : k < 32) :
    ((initialSchedule bits)[i]!).toBitVec.getLsbD k = bits[32 * i + (31 - k)]! := by
  have hword : (initialSchedule bits)[i]! =
      UInt32.ofNat (Reference.bitsToNat (bits.extract (32 * i) (32 * (i + 1)))) := by
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
      ((initialSchedule (Standards.NIST.SHA2.bytesToBits block))[i]!).toBitVec := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [bswap32_memLoad_getLsbD _ _ k hk,
    initialSchedule_getLsbD _ i hi (by rw [bytesToBits_size]; omega) k hk,
    bytesToBits_getElem! _ _ (by omega)]
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
      ((schedule (Standards.NIST.SHA2.bytesToBits block))[i]!).toBitVec := by
  rw [schedule_getElem!_initial _ i hi]
  apply bswap32_memLoad_initialSchedule hbytes i hi
  have hs : block.size = 64 := hbytes.1.trans hsize
  omega

theorem input_word {mem : Ram} {base : BitVec 64} {input : ByteArray}
    (bytes : (⟨base.toNat, input.size⟩ : MemoryRegion).HasBytes mem input)
    {index : Nat} (more : index < input.size / 64) (i : Nat) (hi : i < 16) :
    bswap32 (memLoad mem (base + BitVec.ofNat 64 (64*index) + BitVec.ofNat 64 (4*i)) 32) =
      ((schedule (blockBits input index))[i]!).toBitVec := by
  let r : MemoryRegion := ⟨base.toNat + 64 * index, 64⟩
  have apart : 64 * (index + 1) ≤ input.size := by omega
  have hs : (input.extract (64*index) (64*(index+1))).size = 64 := by
    rw [ByteArray.size_extract]
    omega
  have block : r.HasBytes mem (input.extract (64*index) (64*(index+1))) := by
    refine ⟨hs, ?_⟩
    intro j
    have hj := j.isLt
    have _: j.val < 64 := by omega
    change mem[BitVec.ofNat 64 (base.toNat + 64*index + j.val)]? = _
    rw [Nat.add_assoc]
    have hb := bytes.2 ⟨64*index+j.val, by omega⟩
    simpa only [ByteArray.getElem_extract] using hb
  simpa only [blockBits, r, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
    bswap32_memLoad_schedule block rfl i hi

end K256.Proofs.Verify.Hash.Compression
