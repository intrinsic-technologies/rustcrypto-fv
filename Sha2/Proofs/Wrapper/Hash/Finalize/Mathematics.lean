import Sha2.Proofs.Wrapper.Hash.Finalize.State
import Sha2.Proofs.FIPS180.Computation

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Hash.Finalize

open Sha2.Spec Sha2.Proofs.Program Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.SHA256

theorem length_word (n : Nat) :
    (((BitVec.ofNat 64 (n % 64)).setWidth 32 <<< 3).setWidth 64 |||
      (BitVec.ofNat 64 (n / 64) <<< 9)) = BitVec.ofNat 64 (8 * n) := by
  have rem := Nat.mod_lt n (by decide : 0 < 64)
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or, BitVec.toNat_setWidth, BitVec.toNat_shiftLeft,
    BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.reducePow]
  rw [Nat.mod_eq_of_lt (by omega : n % 64 < 18446744073709551616),
    Nat.mod_eq_of_lt (by omega : n % 64 < 4294967296),
    Nat.mod_eq_of_lt (by omega : n % 64 * 8 < 4294967296),
    Nat.mod_eq_of_lt (by omega : n % 64 * 8 < 18446744073709551616), Nat.mod_mul_mod]
  have blockMod : n / 64 * 512 % 18446744073709551616 =
      n / 64 % 36028797018963968 * 512 := Nat.mul_mod_mul_right 512 (n / 64) 36028797018963968
  rw [blockMod, Nat.or_comm, Nat.mul_comm (n / 64 % 36028797018963968) 512,
    ← Nat.two_pow_add_eq_or_of_lt (i := 9) (by omega : n % 64 * 8 < 2^9)]
  have whole : 8 * n = n % 64 * 8 + (n / 64) * 512 := by omega
  have small := Nat.mod_lt (n / 64) (by decide : 0 < 36028797018963968)
  rw [whole, Nat.add_mod, Nat.mod_eq_of_lt (by omega : n % 64 * 8 < 18446744073709551616), blockMod,
    Nat.mod_eq_of_lt (by omega : n % 64 * 8 + n / 64 % 36028797018963968 * 512 < 18446744073709551616)]
  omega

theorem paddedBuffer_prefix (message : ByteArray) (small : message.size % 64 < 56) :
    (paddedBuffer message).extract 0 56 = finalPrefix message := by
  have count : 63 - message.size % 64 = (55 - message.size % 64) + 8 := by omega
  have split : (⟨Array.replicate (63 - message.size % 64) 0⟩ : ByteArray) =
      ⟨Array.replicate (55 - message.size % 64) 0⟩ ++ ⟨Array.replicate 8 0⟩ := by
    apply ByteArray.ext
    simp only [ByteArray.data_append, Array.replicate_append_replicate, count]
  have size : (finalPrefix message).size = 56 := by
    simp only [finalPrefix, small, ite_true, ByteArray.size_append, remainderBytes_size]
    simp only [ByteArray.size, Array.size_replicate]
    change message.size % 64 + 1 + (55 - message.size % 64) = 56
    omega
  have padded : paddedBuffer message = finalPrefix message ++ ⟨Array.replicate 8 0⟩ := by
    simp only [paddedBuffer, finalPrefix, small, ite_true, split, ByteArray.append_assoc]
  rw [padded]
  exact ByteArray.extract_append_eq_left size.symm

theorem digest_tail_compressions (v : Variant) (message : ByteArray) :
    v.serializeHash (if message.size % 64 < 56 then
      NIST.SHA256.compress (compressBlocks v.initialHash message)
        (NIST.Encoding.octetsToBits (tailFirst message))
    else
      NIST.SHA256.compress
        (NIST.SHA256.compress (compressBlocks v.initialHash message)
          (NIST.Encoding.octetsToBits (tailFirst message)))
        (NIST.Encoding.octetsToBits (tailLast message))) = v.hash message := by
  cases v with
  | sha256 => exact serializeHash_tail_compressions message
  | sha224 =>
    change (serializeHash _).extract 0 28 = _
    rw [serializeHash_tail_compressions_truncated]
    apply ByteArray.ext
    exact Sha2.Proofs.FIPS180.sha224_eq_fips180 message

end Sha2.Proofs.Wrapper.Hash.Finalize
