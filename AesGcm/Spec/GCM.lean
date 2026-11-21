import Standards.NIST.GCM
import Standards.NIST.AES

/-!
# AES-GCM as `aes-gcm` 0.11.1 instantiates it

The crate's two named types, `Aes128Gcm` and `Aes256Gcm`, are GCM (NIST SP 800-38D) with the
AES-128 or AES-256 forward cipher (FIPS 197-upd1), a 96-bit nonce as the IV and a 128-bit tag,
on byte strings. This module converts bytes to the bit strings of `Standards.NIST.GCM` and back,
gives the crate's supported lengths (its `P_MAX` and `A_MAX`), and states each operation the
wrappers reach: authenticated encryption, authenticated decryption, and the tag-after-ciphertext
forms that `aead`'s `AeadInOut::encrypt_in_place` and `decrypt_in_place` use.

Source: https://nvlpubs.nist.gov/nistpubs/Legacy/SP/nistspecialpublication800-38d.pdf
-/

namespace AesGcm.Spec.GCM

open Standards.NIST

/-- The bit string of a byte string, each byte most significant bit first (FIPS 197-upd1, §3.3) -/
def bitsOfByteArray (bytes : ByteArray) : Vector Bool (8 * bytes.size) :=
  GCM.bitsOfBytes ⟨bytes.data, rfl⟩

/-- The byte string of a bit string of `8k` bits, each byte most significant bit first -/
def byteArrayOfBits (bits : Vector Bool (8 * k)) : ByteArray :=
  ⟨(GCM.bytesOfBits bits).toArray⟩

/--
`CIPH_K`, the AES forward cipher under `key` as a function on 128-bit blocks (SP 800-38D, §5.1;
FIPS 197-upd1, §5.1); the crate's `Aes128Gcm` uses `.aes128` and `Aes256Gcm` uses `.aes256`
-/
def forwardCipher (variant : AES.Variant) (key : Vector UInt8 variant.keyBytes) :
    Vector Bool 128 → Vector Bool 128 :=
  fun X => GCM.bitsOfBytes (AES.cipher variant key (GCM.bytesOfBits X))

/--
The crate's limit on the plaintext or ciphertext, in bytes: `P_MAX = 2^36 − 32`, the
`2^39 − 256` bits of SP 800-38D, §5.2.1.1
-/
def maxMessageBytes : Nat := 2 ^ 36 - 32

/--
The crate's limit on the associated data, in bytes: `A_MAX = 2^61 − 1`, the most whole bytes in
the `2^64 − 1` bits of SP 800-38D, §5.2.1.1
-/
def maxAssociatedDataBytes : Nat := 2 ^ 61 - 1

/--
The bit lengths the crate supports (SP 800-38D, §5.2.1.1): a 96-bit IV, the only nonce length of
`Aes128Gcm` and `Aes256Gcm`, and the plaintext and associated data within `P_MAX` and `A_MAX`
bytes; inputs are whole bytes, so a length in bits is a multiple of 8 here
-/
def supportedLengths : GCM.SupportedLengths where
  IV := fun n => n == 96
  P := fun n => n ≤ 8 * maxMessageBytes
  A := fun n => n ≤ 8 * maxAssociatedDataBytes

/--
Whether `encrypt_inout_detached` accepts associated data of `associatedDataBytes` bytes and a
plaintext of `plaintextBytes` bytes: both within `supportedLengths`, so the plaintext is at most
`P_MAX` bytes and the associated data at most `A_MAX` bytes; the crate returns `Err` when
`buffer.len() as u64 > P_MAX || associated_data.len() as u64 > A_MAX` (`aes-gcm` 0.11.1,
`src/lib.rs:267-269`)
-/
def lengthsSupported (associatedDataBytes plaintextBytes : Nat) : Bool :=
  supportedLengths.P (8 * plaintextBytes) && supportedLengths.A (8 * associatedDataBytes)

/--
The ciphertext and the 16-byte tag of GCM-AE (SP 800-38D, §7.1) with tag length 128, or `none`
when `lengthsSupported` rejects the lengths: a plaintext longer than `P_MAX` bytes or associated
data longer than `A_MAX` bytes, for which `encrypt_inout_detached` returns `Err`
-/
def ciphertextAndTag (variant : AES.Variant) (key : Vector UInt8 variant.keyBytes)
    (nonce : Vector UInt8 12) (associatedData plaintext : ByteArray) :
    Option (ByteArray × Vector UInt8 16) :=
  if lengthsSupported associatedData.size plaintext.size then
    let (C, T) := GCM.GCM_AE (forwardCipher variant key) 128 (GCM.bitsOfBytes nonce)
      (bitsOfByteArray plaintext) (bitsOfByteArray associatedData)
    some (byteArrayOfBits C, GCM.bytesOfBits (k := 16) T)
  else
    none

/--
The plaintext of GCM-AD (SP 800-38D, §7.2) with tag length 128 and the crate's supported
lengths, or `none` (`FAIL`) when the tag is not the ciphertext's or a length is unsupported
-/
def authenticPlaintext (variant : AES.Variant) (key : Vector UInt8 variant.keyBytes)
    (nonce : Vector UInt8 12) (associatedData ciphertext : ByteArray) (tag : Vector UInt8 16) :
    Option ByteArray :=
  (GCM.GCM_AD (forwardCipher variant key) 128 supportedLengths (GCM.bitsOfBytes nonce)
    (bitsOfByteArray ciphertext) (bitsOfByteArray associatedData)
    (GCM.bitsOfBytes tag)).map byteArrayOfBits

/--
The plaintext of a ciphertext followed by its 16-byte tag, as `aead`'s
`AeadInOut::decrypt_in_place` takes it for a postfix tag: `none` for fewer than 16 bytes, the
`Err` of `decrypt_in_place` (`aead` 0.6.1, `src/lib.rs:299`), and otherwise
`authenticPlaintext` of the last 16 bytes as the tag and the bytes before them as the ciphertext
-/
def authenticPlaintextOfCiphertextWithTag (variant : AES.Variant)
    (key : Vector UInt8 variant.keyBytes) (nonce : Vector UInt8 12)
    (associatedData sealed : ByteArray) : Option ByteArray :=
  if h : 16 ≤ sealed.size then
    let ciphertext := sealed.extract 0 (sealed.size - 16)
    let tag : Vector UInt8 16 := Vector.ofFn fun i =>
      sealed[sealed.size - 16 + i.val]'(by omega)
    authenticPlaintext variant key nonce associatedData ciphertext tag
  else
    none

end AesGcm.Spec.GCM
