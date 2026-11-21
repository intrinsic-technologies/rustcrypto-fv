import Standards.RFC.ChaCha20Poly1305.ChaCha20
import Standards.RFC.ChaCha20Poly1305.Poly1305

/-!
# AEAD_CHACHA20_POLY1305

The Poly1305 key generation of RFC 8439, §2.6 (`poly1305_key_gen`), and the AEAD construction of
§2.8 (`pad16`, `num_to_8_le_bytes`, the Poly1305 input, `chacha20_aead_encrypt`, and decryption),
for a plaintext and AAD of any length, the empty ones included.

The pseudocode of §2.8.1 builds the nonce as `constant | iv`; the text of §2.8, which §2.3.1 makes
normative over the pseudocode, takes a 96-bit nonce, and so do the functions here. §2.8 describes
decryption in prose only; `chacha20AeadDecrypt` follows that prose. The limits P_MAX and A_MAX of
§2.8 are not imposed: lengths are written modulo 2^64, as `num_to_8_le_bytes` writes 64 bits, and
the ChaCha20 counter is the 32-bit sum of `chacha20Encrypt`.

Source: https://www.rfc-editor.org/rfc/rfc8439.html
-/

namespace Standards.RFC.ChaCha20Poly1305

/--
`poly1305_key_gen(key, nonce)`: the first 32 bytes of `chacha20_block(key, 0, nonce)`, the one-time
Poly1305 key `r | s` (RFC 8439, §2.6.1)
-/
def poly1305KeyGen (key : Vector UInt8 32) (nonce : Vector UInt8 12) : Vector UInt8 32 :=
  let block := chacha20Block key 0 nonce
  Vector.ofFn fun i => block[i.val]

/--
`pad16(x)`: no bytes if the length of `x` is a multiple of 16, otherwise `16 - (len(x) % 16)` zero
bytes (RFC 8439, §2.8.1)
-/
def pad16 (x : ByteArray) : ByteArray :=
  if x.size % 16 = 0 then ByteArray.empty else ⟨Array.replicate (16 - x.size % 16) 0⟩

/--
`num_to_8_le_bytes`, which RFC 8439 §2.8.1 names but does not define: the 64 least significant bits
of the number as 8 bytes, least significant byte first, the "64-bit little-endian integer" of §2.8
-/
def numTo8LeBytes (number : Nat) : ByteArray :=
  ⟨Array.ofFn fun i : Fin 8 => UInt8.ofNat (number / 256 ^ i.val)⟩

/--
`mac_data`, the Poly1305 input of the AEAD (RFC 8439, §§2.8 and 2.8.1): the AAD, `pad16(aad)`, the
ciphertext, `pad16(ciphertext)`, then the lengths of the AAD and of the ciphertext in octets as
64-bit little-endian integers
-/
def aeadMacData (aad ciphertext : ByteArray) : ByteArray :=
  aad ++ pad16 aad ++ ciphertext ++ pad16 ciphertext ++ numTo8LeBytes aad.size ++
    numTo8LeBytes ciphertext.size

/--
`chacha20_aead_encrypt` (RFC 8439, §2.8.1), with the 96-bit nonce of §2.8 in place of
`constant | iv`

Input: an AAD and a plaintext of any length, a 256-bit key and a 96-bit nonce
Output: the ciphertext, of the plaintext's length, and the 16-byte tag

1. `otk = poly1305_key_gen(key, nonce)`.
2. `ciphertext = chacha20_encrypt(key, 1, nonce, plaintext)`.
3. `tag = poly1305_mac(mac_data, otk)`, for the `mac_data` of the AAD and the ciphertext.
-/
def chacha20AeadEncrypt (aad : ByteArray) (key : Vector UInt8 32) (nonce : Vector UInt8 12)
    (plaintext : ByteArray) : ByteArray × Vector UInt8 16 :=
  let otk := poly1305KeyGen key nonce
  let ciphertext := chacha20Encrypt key 1 nonce plaintext
  let tag := poly1305Mac (aeadMacData aad ciphertext) otk
  (ciphertext, tag)

/--
AEAD_CHACHA20_POLY1305 decryption as RFC 8439 §2.8 describes it: the tag is calculated by Poly1305
over the AAD and the ciphertext with the key of `poly1305_key_gen(key, nonce)`, and is compared to
the received tag. If they match, the result is `chacha20_encrypt(key, 1, nonce, ciphertext)`, the
plaintext; otherwise the message is not authenticated and the result is `none`.
-/
def chacha20AeadDecrypt (aad : ByteArray) (key : Vector UInt8 32) (nonce : Vector UInt8 12)
    (ciphertext : ByteArray) (tag : Vector UInt8 16) : Option ByteArray :=
  let otk := poly1305KeyGen key nonce
  if poly1305Mac (aeadMacData aad ciphertext) otk = tag then
    some (chacha20Encrypt key 1 nonce ciphertext)
  else
    none

end Standards.RFC.ChaCha20Poly1305
