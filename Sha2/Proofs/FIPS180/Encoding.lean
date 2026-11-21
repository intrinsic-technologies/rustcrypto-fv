import Standards.NIST.SHA2
import Sha2.Proofs.Common.SHA256.Mathematics.Padding.Encoding

namespace Sha2.Proofs.FIPS180
open Standards.NIST.SHA2
open Sha2.Proofs.Common.SHA256

theorem octetsToBits_singleton (x : UInt8) :
    NIST.Encoding.octetsToBits ⟨#[x]⟩ = (wordToBits x.toBitVec).toArray := by
  apply Array.ext
  · simp [NIST.Encoding.octetsToBits, ByteArray.size]
  · intro i hi hi'
    have hi8 : i < 8 := by simpa using hi'
    simp [NIST.Encoding.octetsToBits, ByteArray.size, wordToBits,
      Nat.div_eq_of_lt hi8, Nat.mod_eq_of_lt hi8, BitVec.getMsbD, BitVec.getLsbD]

theorem octetsToBits_eq_bytesToBits (input : ByteArray) :
    NIST.Encoding.octetsToBits input = bytesToBits input := by
  have h (l : List UInt8) : NIST.Encoding.octetsToBits ⟨l.toArray⟩ = bytesToBits ⟨l.toArray⟩ := by
    induction l with
    | nil => simp [NIST.Encoding.octetsToBits, bytesToBits, ByteArray.size]
    | cons x l ih =>
      have heq : (x :: l).toArray = #[x] ++ l.toArray := by simp
      rw [heq]
      have hba : (⟨#[x]⟩ ++ ⟨l.toArray⟩ : ByteArray) = ⟨#[x] ++ l.toArray⟩ := by
        ext1
        exact ByteArray.data_append
      rw [← hba, octetsToBits_append, ih, octetsToBits_singleton]
      simp [bytesToBits, ByteArray.data_append]
  simpa using h input.data.toList

theorem pad_eq (input : Array Bool) :
    NIST.SHA256.pad input = SHA256.pad input := by
  unfold NIST.SHA256.pad SHA256.pad
  apply congrArg (fun tail : Array Bool => input ++ #[true] ++
    Array.replicate ((448 + 512 - (input.size + 1) % 512) % 512) false ++ tail)
  apply Array.ext
  · simp [wordToBits]
  · intro i hi hi'
    have hi64 : i < 64 := by simpa using hi'
    simp [wordToBits, BitVec.getMsbD, BitVec.getLsbD_ofNat,
      show 63-i < 64 by omega]

theorem foldl_bits_eq (bits : List Bool) (n : Nat) :
    bits.foldl (fun v b => 2*v + if b then 1 else 0) n =
      n * 2^bits.length + (BitVec.ofBoolListBE bits).toNat := by
  induction bits generalizing n with
  | nil => simp [BitVec.ofBoolListBE]
  | cons b bits ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_cons, BitVec.ofBoolListBE, BitVec.toNat_cons',
      Nat.shiftLeft_eq, Nat.pow_succ, Nat.add_mul]
    cases b <;> simp [Nat.mul_assoc, Nat.mul_comm, Nat.add_assoc]

theorem bitsToNat_eq_bitsToWord {w : Nat} (bits : Vector Bool w) :
    NIST.Encoding.bitsToNat bits.toArray = (bitsToWord bits).toNat := by
  simp only [NIST.Encoding.bitsToNat, ← Array.foldl_toList, foldl_bits_eq,
    Nat.zero_mul, Nat.zero_add, bitsToWord, BitVec.toNat_cast, Vector.toList]

end Sha2.Proofs.FIPS180
