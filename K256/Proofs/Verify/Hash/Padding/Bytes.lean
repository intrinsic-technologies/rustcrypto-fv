import K256.Proofs.Verify.Hash.Blocks
import Standards.SECG.ECC.Encoding
import K256.Proofs.Verify.Hash.Padding.Encoding

set_option autoImplicit false

namespace K256.Proofs.Verify.Hash

def paddingZeroBytes (input : ByteArray) : Nat := (55 + 64 - input.size % 64) % 64

def bytePadding (input : ByteArray) : ByteArray :=
  input ++ ⟨#[128]⟩ ++ ⟨Array.replicate (paddingZeroBytes input) 0⟩ ++
    Standards.SECG.ECC.Encoding.natToOctets 8 (8 * input.size)

theorem padding_bit_zeroCount (n : Nat) :
    (448 + 512 - (8 * n + 1) % 512) % 512 =
      7 + 8 * ((55 + 64 - n % 64) % 64) := by
  omega

theorem bytesToBits_bytePadding (input : ByteArray) :
    Standards.NIST.SHA2.bytesToBits (bytePadding input) = Standards.NIST.SHA2.SHA256.pad (Standards.NIST.SHA2.bytesToBits input) := by
  simp only [bytePadding, bytesToBits_append, bytesToBits_paddingMarker,
    bytesToBits_replicate_zero, bytesToBits_natToOctets, Standards.NIST.SHA2.SHA256.pad,
    wordToBits_ofNat,
    bytesToBits_size, padding_bit_zeroCount, paddingZeroBytes]
  simp only [Array.append_assoc]
  rw [← Array.append_assoc (xs := Array.replicate 7 false), Array.replicate_append_replicate]

end K256.Proofs.Verify.Hash
