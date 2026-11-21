/-!
# Poly1305

The Poly1305 one-time authenticator of RFC 8439, §2.5, in the pseudocode of §2.5.1 with verified
Erratum 5689: clamping of `r`, the little-endian conversions `le_bytes_to_num` and
`num_to_16_le_bytes`, and `poly1305_mac` of a message of any length, the empty message included,
under a 32-byte one-time key. §2.5 credits the algorithm to D. J. Bernstein, "The Poly1305-AES
message-authentication code" (March 2005, http://cr.yp.to/mac/poly1305-20050329.pdf), whose MAC
encrypts a nonce with AES to obtain `s`; that construction is not formalized.

Erratum: https://www.rfc-editor.org/errata/eid5689

Source: https://www.rfc-editor.org/rfc/rfc8439.html
-/

namespace Standards.RFC.ChaCha20Poly1305

/--
`le_bytes_to_num`, which RFC 8439 §2.5.1 names but does not define: the bytes as a number, least
significant byte first. §2.5 gives its meaning: "Read the block as a little-endian number", and for
the key half, '"r" is treated as a 16-octet little-endian number'. The RFC states nothing for the
empty string, which its pseudocode never converts; this definition gives zero.
-/
def leBytesToNum (bytes : ByteArray) : Nat :=
  bytes.data.foldr (fun byte number => byte.toNat + 256 * number) 0

/--
`num_to_16_le_bytes`, which RFC 8439 §2.5.1 names but does not define: the 128 least significant
bits of the number as 16 bytes, least significant byte first. Its meaning is §2.5's "the 128 least
significant bits are serialized in little-endian order to form the tag".
-/
def numTo16LeBytes (number : Nat) : Vector UInt8 16 :=
  Vector.ofFn fun i => UInt8.ofNat (number / 256 ^ i.val)

/--
`clamp(r)`: `r &= 0x0ffffffc0ffffffc0ffffffc0fffffff`, which clears the top four bits of bytes 3,
7, 11 and 15 of `r` and the bottom two bits of bytes 4, 8 and 12 (RFC 8439, §§2.5 and 2.5.1)
-/
def clamp (r : Nat) : Nat := r &&& 0x0ffffffc0ffffffc0ffffffc0fffffff

/--
`poly1305_mac` (RFC 8439, §2.5.1, with verified Erratum 5689)

Input: a message `msg` of any number of bytes and a 32-byte one-time key `key`
Output: the 16-byte tag

1. `r` is key bytes 0 to 15 as a little-endian number, clamped; `s` is key bytes 16 to 31.
2. The accumulator `a` starts at zero, and `p = 2^130 - 5`.
3. For each block `i` of 16 message bytes, the last one possibly shorter (bytes `16(i-1)` to
   `min(16i - 1, length - 1)`), `n` is the block with the byte `0x01` appended, as a little-endian
   number; then `a += n` and `a = (r * a) % p`.
4. `a += s`, and the tag is `num_to_16_le_bytes(a)`.
-/
def poly1305Mac (msg : ByteArray) (key : Vector UInt8 32) : Vector UInt8 16 := Id.run do
  let r := clamp (leBytesToNum ⟨key.toArray.extract 0 16⟩)
  let s := leBytesToNum ⟨key.toArray.extract 16 32⟩
  let mut a := 0
  let p := 2 ^ 130 - 5
  for i in [1:(msg.size + 15) / 16 + 1] do
    let j := min (i * 16 - 1) (msg.size - 1)
    let n := leBytesToNum (msg.extract ((i - 1) * 16) (j + 1) ++ ⟨#[0x01]⟩)
    a := a + n
    a := (r * a) % p
  a := a + s
  return numTo16LeBytes a

end Standards.RFC.ChaCha20Poly1305
