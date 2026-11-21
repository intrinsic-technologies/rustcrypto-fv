import Sha1.Proofs.Buffered.Finalize.Digest.Blocks
import Sha1.Proofs.Buffered.Finalize.Digest.BlockCopy.Length
import Sha1.Proofs.Wrapper.Hash.LengthEncoding
import X86Proofs.Instructions.Bswap.Operation

namespace Sha1.Proofs.Buffered.Finalize.Digest

open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem storedByte_bswap64 (word : BitVec 64) (i : Nat) (hi : i < 8) :
    storedByte (bswapSpec word) i = storedByte word (7 - i) := by
  have he := congrArg UInt8.ofBitVec
    (lane_ofLanes (n := 64) (w := 8) (fun j => lane 8 word (64 / 8 - 1 - j)) i hi)
  simpa only [bswapSpec, storedByte_eq_extract, lane, Nat.mul_comm,
    Nat.reduceDiv, Nat.reduceSub] using he

theorem getElem_lengthBlockBytes (message : ByteArray) (k : Nat) (hk : k < 8) :
    (lengthBlockBytes message)[k]! = storedByte (lengthWord message) (7 - k) := by
  rw [getElem!_pos (lengthBlockBytes message) k (by rw [size_lengthBlockBytes]; exact hk)]
  simp only [lengthBlockBytes, ByteArray.getElem_eq_getElem_data, Array.getElem_ofFn]
  rw [storedByte_eq_extract]
  congr 1

theorem lengthValue_eq {s : RamState} {message : ByteArray}
    (h15 : (Operand.reg 15 : Operand 64).read s = BitVec.ofNat 64 (message.size % 64))
    (h12 : (Operand.reg 12 : Operand 64).read s = BitVec.ofNat 64 (message.size / 64)) :
    BlockCopy.lengthValue s = bswapSpec (lengthWord message) := by
  have h32 : (Operand.reg 15 : Operand 32).read s = BitVec.ofNat 32 (message.size % 64) := by
    have he : (Operand.reg 15 : Operand 32).read s =
        ((Operand.reg 15 : Operand 64).read s).setWidth 32 := rfl
    rw [he, h15]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  rw [BlockCopy.lengthValue, h32, h12, Sha1.Proofs.Wrapper.Hash.tail_shift_or_blocks]
  rfl

theorem lengthValue_bytes {s : RamState} {message : ByteArray}
    (h15 : (Operand.reg 15 : Operand 64).read s = BitVec.ofNat 64 (message.size % 64))
    (h12 : (Operand.reg 12 : Operand 64).read s = BitVec.ofNat 64 (message.size / 64))
    (k : Nat) (hk : k < 8) :
    storedByte (BlockCopy.lengthValue s) k = (lengthBlockBytes message)[k]! := by
  rw [lengthValue_eq h15 h12, storedByte_bswap64 _ k hk, getElem_lengthBlockBytes _ k hk]

theorem getElem_lastBlock_prefix (message : ByteArray) (i : Nat) (hi : i < 56) :
    (lastBlock message)[i]! =
      if message.size % 64 < 56 then (firstBlock message)[i]! else 0 := by
  rw [getElem!_pos (lastBlock message) i (by rw [size_lastBlock]; omega)]
  unfold lastBlock
  rw [ByteArray.getElem_append_left (by split <;> simp [ByteArray.size_extract] <;> omega)]
  split
  · rw [getElem!_pos (firstBlock message) i (by rw [size_firstBlock]; omega)]
    simp only [ByteArray.getElem_extract, Nat.zero_add]
  · simp only [padZeros, ByteArray.getElem_eq_getElem_data, Array.getElem_replicate]

theorem getElem_lastBlock_length (message : ByteArray) (k : Nat) (hk : k < 8) :
    (lastBlock message)[56 + k]! = (lengthBlockBytes message)[k]! := by
  rw [getElem!_pos (lastBlock message) (56 + k) (by rw [size_lastBlock]; omega),
    getElem!_pos (lengthBlockBytes message) k (by rw [size_lengthBlockBytes]; omega)]
  unfold lastBlock
  rw [ByteArray.getElem_append_right (by split <;> simp [ByteArray.size_extract])]
  congr 1
  split <;> simp [ByteArray.size_extract]

theorem lastBlock_bytes {m : Ram} {base : BitVec 64} (message : ByteArray)
    (hPrefix : ∀ i < 56, m[base + BitVec.ofNat 64 i]? =
      some (if message.size % 64 < 56 then (firstBlock message)[i]! else 0))
    (hLength : ∀ k < 8, m[base + BitVec.ofNat 64 (56 + k)]? =
      some ((lengthBlockBytes message)[k]!)) :
    Bytes m base 64 (fun i ↦ (lastBlock message)[i]!) := by
  intro i hi
  dsimp only
  by_cases h56 : i < 56
  · rw [getElem_lastBlock_prefix message i h56]
    exact hPrefix i h56
  · have := hLength (i - 56) (by omega)
    rw [show 56 + (i - 56) = i by omega] at this
    rw [this, ← getElem_lastBlock_length message (i - 56) (by omega),
      show 56 + (i - 56) = i by omega]

end Sha1.Proofs.Buffered.Finalize.Digest
