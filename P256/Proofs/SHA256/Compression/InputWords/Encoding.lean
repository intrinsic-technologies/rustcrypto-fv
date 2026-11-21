import P256.Proofs.SHA256.Interface
import Init.Data.ByteArray.Lemmas
import Init.Data.Nat.Bitwise.Lemmas

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression

open P256.Proofs.SHA256

theorem octetsToBits_size (input : ByteArray) :
    (Standards.NIST.SHA2.bytesToBits input).size = 8 * input.size := by
  change (((⟨input.data, rfl⟩ : Vector UInt8 input.size).flatMap
    (fun x => Standards.NIST.SHA2.wordToBits x.toBitVec)).toArray).size = _
  rw [Vector.size_toArray, Nat.mul_comm]

theorem octetsToBits_getElem! (input : ByteArray) (i : Nat) (hi : i < 8 * input.size) :
    (Standards.NIST.SHA2.bytesToBits input)[i]! = input.data[i / 8]!.toNat.testBit (7 - i % 8) := by
  have hi' : i < input.size * 8 := by omega
  have hdiv : i / 8 < input.data.size := by change i / 8 < input.size; omega
  change (((⟨input.data, rfl⟩ : Vector UInt8 input.size).flatMap
    (fun x => Standards.NIST.SHA2.wordToBits x.toBitVec)).toArray)[i]! = _
  rw [getElem!_pos _ i (by simpa only [Vector.size_toArray] using hi'),
    Vector.getElem_toArray, Vector.getElem_flatMap, getElem!_pos input.data (i / 8) hdiv]
  simp [Standards.NIST.SHA2.wordToBits, BitVec.getMsbD, BitVec.getLsbD]

theorem bitsToNat_testBit (bits : Array Bool) (i : Nat) (hi : i < bits.size) :
    (Reference.bitsToNat bits).testBit i = bits[bits.size - 1 - i]! := by
  change (BitVec.ofBoolListBE bits.toList).getLsbD i = _
  rw [BitVec.getLsbD_ofBoolListBE]
  simp [hi, List.getD, getElem!_pos,
    show bits.size - 1 - i < bits.size by omega]

end P256.Proofs.SHA256.Compression
