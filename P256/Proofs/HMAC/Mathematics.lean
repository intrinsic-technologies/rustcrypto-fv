import P256.Spec.Operations
import Standards.RFC.HMAC

set_option autoImplicit false

namespace P256.Proofs.HMAC

open P256.Spec

def keyPad (key : ByteArray) (pad : UInt8) : ByteArray :=
  ⟨(Array.range 64).map fun i => key.data[i]?.getD 0 ^^^ pad⟩

theorem keyPad_size (key : ByteArray) (pad : UInt8) : (keyPad key pad).size = 64 := by
  simp only [keyPad, ByteArray.size, Array.size_map, Array.size_range]

theorem keyPad_getElem (key : ByteArray) (pad : UInt8) (i : Nat) (hi : i < 64) :
    (keyPad key pad)[i]'(by rw [keyPad_size]; exact hi) = key.data[i]?.getD 0 ^^^ pad := by
  simp only [keyPad, ByteArray.getElem_eq_getElem_data, Array.getElem_map, Array.getElem_range]

theorem keyPad_getElem_key (key : ByteArray) (pad : UInt8) (i : Nat)
    (hi : i < 64) (hk : i < key.size) :
    (keyPad key pad)[i]'(by rw [keyPad_size]; exact hi) = key[i] ^^^ pad := by
  rw [keyPad_getElem key pad i hi]
  simp only [show i < key.data.size from hk, getElem?_pos, Option.getD_some]
  rfl

theorem keyPad_getElem_padding (key : ByteArray) (pad : UInt8) (i : Nat)
    (hi : i < 64) (hk : key.size ≤ i) :
    (keyPad key pad)[i]'(by rw [keyPad_size]; exact hi) = pad := by
  rw [keyPad_getElem key pad i hi]
  simp only [getElem?_neg key.data i (by exact Nat.not_lt.mpr hk), Option.getD_none,
    UInt8.zero_xor]

theorem hmacSha256_eq (key input : ByteArray) (hk : key.size ≤ 64) :
    Standards.RFC.HMAC.hmac Operations.hash 64 key input =
      Operations.hash (keyPad key 0x5c ++
        Operations.hash (keyPad key 0x36 ++ input)) := by
  simp only [Standards.RFC.HMAC.hmac, Nat.not_lt.mpr hk, ↓reduceIte, keyPad]

theorem hash_size (input : ByteArray) : (Operations.hash input).size = 32 := by
  change (Standards.NIST.SHA2.SHA256 (Standards.NIST.SHA2.bytesToBits input)).bytes.toArray.size = 32
  exact Vector.size_toArray _

theorem hmac_size (key input : ByteArray) :
    (Standards.RFC.HMAC.hmac Operations.hash 64 key input).size = 32 := by
  unfold Standards.RFC.HMAC.hmac
  exact hash_size _

theorem inner_remainder_lt (key input : ByteArray)
    (hi : input.size = 32 ∨ input.size = 33 ∨ input.size = 97) :
    (keyPad key 0x36 ++ input).size % 64 < 56 := by
  rw [ByteArray.size_append, keyPad_size]
  omega

end P256.Proofs.HMAC
