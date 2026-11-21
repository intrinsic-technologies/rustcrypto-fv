import Sha1.Proofs.Compress.Parser
import X86Proofs.Program.ReadWrite.Bytes
import X86Proofs.Instructions.Bswap.Operation
import Prelude.Memory.Region

namespace Sha1.Proofs.Compress.Input

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Standards.NIST.SHA2

theorem storedByte_bswap32 (word : BitVec 32) (i : Nat) (hi : i < 4) :
    storedByte (bswapSpec word) i = storedByte word (3 - i) := by
  have he := congrArg UInt8.ofBitVec
    (lane_ofLanes (n := 32) (w := 8) (fun j => lane 8 word (32 / 8 - 1 - j)) i hi)
  simpa only [bswapSpec, storedByte_eq_extract, lane, Nat.mul_comm,
    Nat.reduceDiv, Nat.reduceSub] using he

theorem storedByte_bswap_blockWord (bytes : ByteArray) (block word i : Nat) (hi : i < 4) :
    storedByte (bswapSpec (Parser.blockWord bytes block word)) i =
      bytes[64 * block + 4 * word + i]?.getD 0 := by
  rw [storedByte_bswap32 _ i hi]
  apply UInt8.eq_of_toBitVec_eq
  apply BitVec.eq_of_getMsbD_eq
  intro bit hbit
  simp only [storedByte_eq_extract, UInt8.toBitVec_ofBitVec, BitVec.getMsbD_extractLsb',
    hbit, show 8 * (3 - i) + 8 - bit ≤ 32 by omega, decide_true, Bool.true_and]
  rw [show 32 - (8 * (3 - i) + 8 - bit) = 8 * i + bit by omega,
    Parser.blockWord_getMsbD _ _ _ _ (by omega)]
  rw [show (8 * i + bit) / 8 = i by omega,
    show (8 * i + bit) % 8 = bit by omega]

theorem memLoad_blockWord {memory : Ram} {base : BitVec 64} {bytes : ByteArray}
    (hbytes : Bytes memory base bytes.size (fun i => bytes[i]?.getD 0))
    (block word : Nat) (hblock : block < bytes.size / 64) (hword : word < 16) :
    memLoad memory (base + BitVec.ofNat 64 (64 * block + 4 * word)) 32 =
      bswapSpec (Parser.blockWord bytes block word) := by
  have hwindow := hbytes.sub (64 * block + 4 * word) 4 (by omega)
  apply Bytes.memLoad (n := 32) _ (by decide) (by decide)
  apply hwindow.congr
  intro i hi
  exact (storedByte_bswap_blockWord bytes block word i hi).symm

theorem memLoad_parse {memory : Ram} {region : MemoryRegion} {bytes : ByteArray}
    (hbytes : region.HasBytes memory bytes) (block word : Nat)
    (hblock : block < bytes.size / 64) (hword : word < 16) :
    memLoad memory (BitVec.ofNat 64 region.start + BitVec.ofNat 64 (64 * block + 4 * word)) 32 =
      bswapSpec (((SHA256.parse (bytesToBits bytes))[block]'(by
        rw [Parser.parse_size]
        exact hblock))[word]) := by
  rw [Parser.parse_getElem bytes block word hblock hword]
  apply memLoad_blockWord (block := block) (word := word) _ hblock hword
  intro i hi
  have he := hbytes.2 ⟨i, hi⟩
  rw [BitVec.ofNat_add] at he
  simpa only [getElem?_pos bytes i hi, Option.getD_some] using he

theorem memLoad_parse_at {memory : Ram} {base : BitVec 64} {bytes : ByteArray}
    (hbytes : (MemoryRegion.mk base.toNat bytes.size).HasBytes memory bytes)
    (block word : Nat) (hblock : block < bytes.size / 64) (hword : word < 16) :
    memLoad memory (base + BitVec.ofNat 64 (64 * block + 4 * word)) 32 =
      bswapSpec (((SHA256.parse (bytesToBits bytes))[block]'(by
        rw [Parser.parse_size]
        exact hblock))[word]) := by
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
    memLoad_parse hbytes block word hblock hword

def firstBlock (bytes : ByteArray) : Vector (BitVec 32) 16 :=
  (SHA256.parse (bytesToBits bytes))[0]?.getD (Vector.replicate 16 0)

theorem firstBlock_getElem (bytes : ByteArray) (hsize : 64 ≤ bytes.size)
    (word : Nat) (hword : word < 16) :
    (firstBlock bytes)[word] = Parser.blockWord bytes 0 word := by
  simp only [firstBlock,
    getElem?_pos (SHA256.parse (bytesToBits bytes)) 0 (by rw [Parser.parse_size]; omega),
    Option.getD_some]
  exact Parser.parse_getElem bytes 0 word (by omega) hword

theorem parse_tail (bytes : ByteArray) (hsize : 64 ≤ bytes.size) :
    SHA256.parse (bytesToBits bytes) =
      #[firstBlock bytes] ++ SHA256.parse (bytesToBits (bytes.extract 64 bytes.size)) := by
  have hsplit : bytes.extract 0 64 ++ bytes.extract 64 bytes.size = bytes := by
    rw [ByteArray.extract_append_extract, Nat.min_eq_left (Nat.zero_le _),
      Nat.max_eq_right hsize, ByteArray.extract_zero_size]
  have hprefix : (bytes.extract 0 64).size = 64 := by
    simp only [ByteArray.size_extract, Nat.min_eq_left hsize, Nat.sub_zero]
  have hparsed : (SHA256.parse (bytesToBits (bytes.extract 0 64))).size = 1 := by
    rw [Parser.parse_size, hprefix]
  have hfull : SHA256.parse (bytesToBits bytes) =
      SHA256.parse (bytesToBits (bytes.extract 0 64)) ++
        SHA256.parse (bytesToBits (bytes.extract 64 bytes.size)) := by
    rw [← Parser.parse_append _ _ (by omega), hsplit]
  have hfirst : firstBlock bytes =
      (SHA256.parse (bytesToBits (bytes.extract 0 64)))[0]'(by rw [hparsed]; decide) := by
    simp only [firstBlock, hfull]
    rw [getElem?_pos (SHA256.parse (bytesToBits (bytes.extract 0 64)) ++
      SHA256.parse (bytesToBits (bytes.extract 64 bytes.size))) 0
      (by rw [Array.size_append, hparsed]; omega), Option.getD_some,
      Array.getElem_append_left (by rw [hparsed]; decide)]
  have hsingle : SHA256.parse (bytesToBits (bytes.extract 0 64)) = #[firstBlock bytes] := by
    apply Array.ext
    · simpa only [Array.size_singleton] using hparsed
    · intro i hi hi'
      have hi0 : i = 0 := by rw [hparsed] at hi; omega
      subst i
      simpa only [Array.getElem_singleton] using hfirst.symm
  rw [hfull, hsingle]

theorem parse_foldl_tail {α : Type} (step : α → Vector (BitVec 32) 16 → α)
    (initial : α) (bytes : ByteArray) (hsize : 64 ≤ bytes.size) :
    (SHA256.parse (bytesToBits bytes)).foldl step initial =
      (SHA256.parse (bytesToBits (bytes.extract 64 bytes.size))).foldl step
        (step initial (firstBlock bytes)) := by
  rw [parse_tail bytes hsize, Array.foldl_append]
  rfl

end Sha1.Proofs.Compress.Input
