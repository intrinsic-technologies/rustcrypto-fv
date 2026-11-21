import Standards.RFC.ChaCha20Poly1305.AEAD

/-!
# The message forms of chacha20poly1305's `ChaCha20Poly1305`

What the `ChaCha20Poly1305` type of chacha20poly1305 0.11.0 returns, in terms of RFC 8439's
AEAD_CHACHA20_POLY1305 in `Standards/RFC/ChaCha20Poly1305/AEAD.lean`: the forms that keep the tag
after the ciphertext in one buffer (`encryptWithTag`, `decryptWithTag`), the order of RFC 8439 §2.8,
which aead's `TagPosition::Postfix` keeps, and what `encrypt_in_place` leaves in a buffer with no
room for the tag (`encryptWithoutTag`).

No specification here has the crate's message-length check (`cipher.rs`, lines 58 and 81): every
buffer of a valid call lies below 4 GiB, where the check never fires.

Source: https://www.rfc-editor.org/rfc/rfc8439.html#section-2.8
-/

namespace ChaCha20Poly1305.Spec.AEAD

open Standards.RFC.ChaCha20Poly1305

/--
The ciphertext of `chacha20AeadEncrypt` followed by its 16-byte tag: what `Aead::encrypt` returns
and what `AeadInOut::encrypt_in_place` leaves in a buffer with room for the tag, with the tag last
as aead's `TagPosition::Postfix` places it (RFC 8439, §2.8)
-/
def encryptWithTag (associatedData : ByteArray) (key : Vector UInt8 32) (nonce : Vector UInt8 12)
    (plaintext : ByteArray) : ByteArray :=
  let (ciphertext, tag) := chacha20AeadEncrypt associatedData key nonce plaintext
  ciphertext ++ ⟨tag.toArray⟩

/--
The ciphertext of `chacha20AeadEncrypt` alone, without its tag, which is
`chacha20Encrypt key 1 nonce plaintext` (RFC 8439, §2.8): what `AeadInOut::encrypt_in_place`
leaves in a buffer with no room for the tag, because it encrypts the message where it lies before
it appends the tag (aead 0.6.1 `src/lib.rs`, lines 276-278), and appending to the wrappers'
`SliceBuffer` without room returns `aead::Error`, writing nothing
-/
def encryptWithoutTag (associatedData : ByteArray) (key : Vector UInt8 32)
    (nonce : Vector UInt8 12) (plaintext : ByteArray) : ByteArray :=
  let (ciphertext, _) := chacha20AeadEncrypt associatedData key nonce plaintext
  ciphertext

/--
Decryption of a ciphertext followed by its 16-byte tag, as `Aead::decrypt` and
`AeadInOut::decrypt_in_place` take it: `none` if the input is shorter than the tag (aead's
`checked_sub`, which returns the crate's one error), otherwise `chacha20AeadDecrypt` of all but the
last 16 bytes under those 16 bytes as the tag (RFC 8439, §2.8)
-/
def decryptWithTag (associatedData : ByteArray) (key : Vector UInt8 32) (nonce : Vector UInt8 12)
    (ciphertextWithTag : ByteArray) : Option ByteArray :=
  if h : 16 ≤ ciphertextWithTag.size then
    let ciphertextSize := ciphertextWithTag.size - 16
    let ciphertext := ciphertextWithTag.extract 0 ciphertextSize
    let tag : Vector UInt8 16 := Vector.ofFn fun i =>
      ciphertextWithTag[ciphertextSize + i.val]'(by omega)
    chacha20AeadDecrypt associatedData key nonce ciphertext tag
  else
    none

end ChaCha20Poly1305.Spec.AEAD
