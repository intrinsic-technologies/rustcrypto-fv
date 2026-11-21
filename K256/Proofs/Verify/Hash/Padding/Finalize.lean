import K256.Proofs.Verify.Hash.Blocks
import Standards.SECG.ECC.Encoding
import K256.Proofs.Verify.Hash.Padding.Tail

set_option autoImplicit false

namespace K256.Proofs.Verify.Hash

def paddedBuffer (message : ByteArray) : ByteArray :=
  remainderBytes message ++ ⟨#[128]⟩ ++ ⟨Array.replicate (63 - message.size % 64) 0⟩

def finalPrefix (message : ByteArray) : ByteArray :=
  if message.size % 64 < 56 then
    remainderBytes message ++ ⟨#[128]⟩ ++ ⟨Array.replicate (55 - message.size % 64) 0⟩
  else ⟨Array.replicate 56 0⟩

def finalBlock (message : ByteArray) : ByteArray :=
  finalPrefix message ++ Standards.SECG.ECC.Encoding.natToOctets 8 (8 * message.size)

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

theorem paddedBuffer_size (message : ByteArray) : (paddedBuffer message).size = 64 := by
  simp only [paddedBuffer, ByteArray.size_append, remainderBytes_size]
  simp only [ByteArray.size, Array.size_replicate]
  change message.size % 64 + 1 + (63 - message.size % 64) = 64
  omega

theorem finalBlock_eq (message : ByteArray) :
    finalBlock message =
      if message.size % 64 < 56 then tailFirst message else tailLast message := by
  unfold finalBlock finalPrefix tailFirst tailLast
  split <;> rfl

theorem finalBlock_size (message : ByteArray) : (finalBlock message).size = 64 := by
  rw [finalBlock_eq]
  split
  · exact tailFirst_size message
  · exact tailLast_size message

theorem serializeHash_finalize (message : ByteArray) :
    serializeHash (Reference.compress
      (if message.size % 64 < 56 then compressBlocks initialHash message
       else Reference.compress (compressBlocks initialHash message)
         (Standards.NIST.SHA2.bytesToBits (paddedBuffer message)))
      (Standards.NIST.SHA2.bytesToBits (finalBlock message))) =
        Standards.NIST.SHA2.SHA256.hashBytes message := by
  rw [finalBlock_eq]
  have result := serializeHash_tail_compressions message
  by_cases small : message.size % 64 < 56
  · simpa only [small, ite_true] using result
  · simpa only [small, ite_false, tailFirst, paddedBuffer] using result

end K256.Proofs.Verify.Hash
