import Hkdf.Proofs.Common.Streaming

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Prepare

open Hkdf.Proofs.Common Hkdf.Proofs.Common.SHA256

theorem tailFirst_outer (key message : ByteArray) :
    tailFirst (HMAC.xorPad (HMAC.keyBlock key) 0x5c ++
      Standards.NIST.SHA2.SHA256.hashBytes
        (HMAC.xorPad (HMAC.keyBlock key) 0x36 ++ message)) =
      Standards.NIST.SHA2.SHA256.hashBytes
        (HMAC.xorPad (HMAC.keyBlock key) 0x36 ++ message) ++
      ⟨#[128]⟩ ++ ⟨Array.replicate 23 0⟩ ++
      Hkdf.Proofs.NIST.Encoding.natToOctets 8 768 := by
  have size : (HMAC.xorPad (HMAC.keyBlock key) 0x5c ++
      Standards.NIST.SHA2.SHA256.hashBytes
        (HMAC.xorPad (HMAC.keyBlock key) 0x36 ++ message)).size = 96 := by
    rw [ByteArray.size_append, HMAC.xorPad_keyBlock_size, HMAC.sha256_hashBytes_size]
  rw [tailFirst, size]
  simp only [Nat.reduceMod, Nat.reduceLT, ↓reduceIte, Nat.reduceSub, Nat.reduceMul]
  rw [remainderBytes_append_aligned _ _
    (by rw [HMAC.xorPad_keyBlock_size])]
  have short : (Standards.NIST.SHA2.SHA256.hashBytes
      (HMAC.xorPad (HMAC.keyBlock key) 0x36 ++ message)).size < 64 := by
    rw [HMAC.sha256_hashBytes_size]
    decide
  simp only [remainderBytes, Nat.div_eq_of_lt short, Nat.mul_zero, ByteArray.extract_zero_size]

end Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Prepare
