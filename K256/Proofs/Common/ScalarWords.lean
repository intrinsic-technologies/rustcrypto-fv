import Standards.SECG.ECC.Encoding
import X86Proofs.Instructions.Bswap.Operation
import X86Proofs.Program.ReadWrite.Bytes
import Prelude.Memory.Region

namespace K256.Proofs.Common

open Prelude X86.Machine X86Proofs Standards.SECG.ECC

def scalarWord (mem : Ram) (base : BitVec 64) (i : Nat) : BitVec 64 :=
  bswapSpec (memLoad mem (base + BitVec.ofNat 64 (8 * (3 - i))) 64)

private theorem foldl_octets_acc (octets : List UInt8) (acc : Nat) :
    octets.foldl (fun value byte => 256 * value + byte.toNat) acc =
      acc * 256 ^ octets.length +
        octets.foldl (fun value byte => 256 * value + byte.toNat) 0 := by
  induction octets generalizing acc with
  | nil => simp
  | cons byte octets ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih (256 * acc + byte.toNat), ih (256 * 0 + byte.toNat), Nat.pow_succ]
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_mul]
    ac_rfl

private theorem octetsToNat_append (left right : ByteArray) :
    Encoding.octetsToNat (left ++ right) =
      Encoding.octetsToNat left * 256 ^ right.size + Encoding.octetsToNat right := by
  simp only [Encoding.octetsToNat, ByteArray.data_append, ← Array.foldl_toList,
    Array.toList_append, List.foldl_append]
  rw [foldl_octets_acc, Array.length_toList, ByteArray.size_data]

private theorem foldl_octets_eq_flattenList (octets : List UInt8) :
    octets.foldl (fun value byte => 256 * value + byte.toNat) 0 =
      (BitVec.flattenList (octets.map UInt8.toBitVec)).toNat := by
  induction octets with
  | nil => rfl
  | cons byte octets ih =>
    have hflatten : (BitVec.flattenList ((byte :: octets).map UInt8.toBitVec)).toNat =
        byte.toNat <<< (8 * (octets.map UInt8.toBitVec).length) |||
          (BitVec.flattenList (octets.map UInt8.toBitVec)).toNat := by
      change (BitVec.flattenList (byte.toBitVec :: octets.map UInt8.toBitVec)).toNat = _
      simp only [BitVec.flattenList, BitVec.toNat_cast, BitVec.toNat_append]
      rfl
    rw [List.foldl_cons, Nat.mul_zero, Nat.zero_add, hflatten, foldl_octets_acc, ih,
      ← Nat.shiftLeft_add_eq_or_of_lt (BitVec.isLt _)]
    simp only [Nat.shiftLeft_eq, List.length_map, Nat.pow_mul]

private theorem bswap_memLoad_getLsbD (mem : Ram) (addr : BitVec 64) (k : Nat) (hk : k < 64) :
    (bswapSpec (memLoad mem addr 64)).getLsbD k =
      (memByte mem (addr + BitVec.ofNat 64 (7 - k / 8))).toBitVec.getLsbD (k % 8) := by
  rw [bswapSpec, getLsbD_ofLanes _ _ hk, ite_eq_left hk]
  have hb := congrArg UInt8.toBitVec (storedByte_memLoad mem addr (n := 64) (7 - k / 8) (by omega))
  rw [storedByte_eq_extract, UInt8.toBitVec_ofBitVec] at hb
  rw [lane, Nat.mul_comm, hb]

private theorem octetsToNat_extract_eq_word {mem : Ram} {region : MemoryRegion} {bytes : ByteArray}
    (hBytes : region.HasBytes mem bytes) {off : Nat} (h : off + 8 ≤ bytes.size) :
    Encoding.octetsToNat (bytes.extract off (off + 8)) =
      (bswapSpec (memLoad mem (BitVec.ofNat 64 (region.start + off)) 64)).toNat := by
  let octets := (bytes.extract off (off + 8)).data.toList
  have hsize : octets.length = 8 := by
    simp only [octets, Array.length_toList, ByteArray.size_data, ByteArray.size_extract,
      Nat.min_eq_left h, Nat.add_sub_cancel_left]
  have hwidth : 8 * (octets.map UInt8.toBitVec).length = 64 := by
    rw [List.length_map, hsize]
  have hword : (BitVec.flattenList (octets.map UInt8.toBitVec)).cast hwidth =
      bswapSpec (memLoad mem (BitVec.ofNat 64 (region.start + off)) 64) := by
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    rw [BitVec.getLsbD_cast, BitVec.getLsbD_flattenList, List.length_map, hsize,
      bswap_memLoad_getLsbD _ _ _ hk]
    have hidx : 7 - k / 8 < (octets.map UInt8.toBitVec).length := by
      rw [List.length_map, hsize]
      omega
    simp only [show k < 8 * 8 by exact hk, decide_true, Bool.true_and,
      List.getElem?_eq_getElem hidx, Option.getD_some, List.getElem_map]
    have hi : off + (7 - k / 8) < bytes.size := by omega
    have hm := hBytes.2 ⟨off + (7 - k / 8), hi⟩
    change mem[BitVec.ofNat 64 (region.start + (off + (7 - k / 8)))]? =
      some bytes[off + (7 - k / 8)] at hm
    rw [← BitVec.ofNat_add, Nat.add_assoc, memByte]
    simp only [PhysicalMemory.read, hm, Option.getD_some]
    simp only [octets, Array.getElem_toList,
      ← ByteArray.getElem_eq_getElem_data, ByteArray.getElem_extract]
  simp only [Encoding.octetsToNat, ← Array.foldl_toList, foldl_octets_eq_flattenList]
  exact congrArg (BitVec.toNat (w := 64)) hword

theorem octetsToNat_extract_eq_words {mem : Ram} {region : MemoryRegion} {bytes : ByteArray}
    (hBytes : region.HasBytes mem bytes) {off : Nat} (h : off + 32 ≤ bytes.size) :
    let word := scalarWord mem (BitVec.ofNat 64 (region.start + off))
    Encoding.octetsToNat (bytes.extract off (off + 32)) =
      ((word 3).toNat * 2^64 + (word 2).toNat) * 2^128 +
        (word 1).toNat * 2^64 + (word 0).toNat := by
  dsimp only [scalarWord]
  rw [ByteArray.extract_eq_extract_append_extract (off + 24) (by omega) (by omega),
    ByteArray.extract_eq_extract_append_extract (off + 16) (by omega) (by omega),
    ByteArray.extract_eq_extract_append_extract (off + 8) (by omega) (by omega)]
  simp only [octetsToNat_append, ByteArray.size_extract,
    Nat.min_eq_left (show off + 16 ≤ bytes.size by omega),
    Nat.min_eq_left (show off + 24 ≤ bytes.size by omega), Nat.min_eq_left h]
  have hword (i : Nat) (hi : i < 4) :
      Encoding.octetsToNat (bytes.extract (off + 8 * i) (off + 8 * (i + 1))) =
        (bswapSpec (memLoad mem (BitVec.ofNat 64 (region.start + off) + BitVec.ofNat 64 (8 * i))
          64)).toNat := by
    rw [← BitVec.ofNat_add, Nat.add_assoc, Nat.mul_succ]
    exact octetsToNat_extract_eq_word hBytes (by omega)
  have h0 := hword 0 (by decide)
  have h1 := hword 1 (by decide)
  have h2 := hword 2 (by decide)
  have h3 := hword 3 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero] at h0
  rw [h0, h1, h2, h3, show off + 16 - (off + 8) = 8 by omega,
    show off + 24 - (off + 16) = 8 by omega, show off + 32 - (off + 24) = 8 by omega]
  simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceMul]
  omega

end K256.Proofs.Common
