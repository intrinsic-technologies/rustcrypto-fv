import Sha2.Proofs.Common.SHA512.Mathematics.Padding.Encoding

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512
open Sha2.Proofs.NIST

def paddingZeroBytes (input : ByteArray) : Nat := (111 + 128 - input.size % 128) % 128

def bytePadding (input : ByteArray) : ByteArray :=
  input ++ ⟨#[128]⟩ ++ ⟨Array.replicate (paddingZeroBytes input) 0⟩ ++
    Encoding.natToOctets 16 (8 * input.size)

theorem padding_bit_zeroCount (n : Nat) :
    (896 + 1024 - (8 * n + 1) % 1024) % 1024 =
      7 + 8 * ((111 + 128 - n % 128) % 128) := by
  omega

theorem octetsToBits_bytePadding (input : ByteArray) :
    Encoding.octetsToBits (bytePadding input) = SHA512.pad (Encoding.octetsToBits input) := by
  simp only [bytePadding, octetsToBits_append, octetsToBits_paddingMarker,
    octetsToBits_replicate_zero, octetsToBits_natToOctets, SHA512.pad,
    octetsToBits_size, padding_bit_zeroCount, paddingZeroBytes]
  simp only [Array.append_assoc]
  rw [← Array.append_assoc (xs := Array.replicate 7 false), Array.replicate_append_replicate]

theorem bytePadding_size (input : ByteArray) :
    (bytePadding input).size = input.size + 1 + paddingZeroBytes input + 16 := by
  simp only [bytePadding, ByteArray.size_append]
  simp only [ByteArray.size, Array.size_replicate, Encoding.natToOctets,
    Array.size_map, Array.size_range]
  rfl

theorem bytePadding_size_mod (input : ByteArray) : (bytePadding input).size % 128 = 0 := by
  rw [bytePadding_size, paddingZeroBytes]
  omega

end Sha2.Proofs.Common.SHA512
