import Standards.NIST.SHA1.Computation
import Standards.NIST.SHA2.Digest
import Standards.NIST.SHA2.Preprocessing

/-!
# FIPS 180-4: SHA-1

The SHA-1 construction in FIPS 180-4, §6.1, for messages of fewer than 2^64 bits. The definitions
are total; padding encodes the bit length modulo 2^64. SHA-1 pads and parses messages as SHA-256
does (§5.1.1 and §5.2.1), and its digest is a `Standards.NIST.SHA2.Digest` of 20 bytes.

Source: https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf
-/

namespace Standards.NIST.SHA1

open Standards.NIST.SHA2

/--
Concatenates the five words of a final hash value into a digest, most significant byte first
(FIPS 180-4, §6.1.2)
-/
def toDigest (H : Vector (BitVec 32) 5) : Digest 20 :=
  ⟨Vector.ofFn fun i =>
    UInt8.ofBitVec ((H[i.val / 4]'(by omega) >>> (8 * (3 - i.val % 4))).setWidth 8)⟩

/-- The SHA-1 message digest of a message of any number of bits (FIPS 180-4, §6.1) -/
def SHA1 (M : Array Bool) : Digest 20 :=
  toDigest (hashComputation (SHA256.parse (SHA256.pad M)))

end Standards.NIST.SHA1
