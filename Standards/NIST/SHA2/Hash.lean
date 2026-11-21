import Standards.NIST.SHA2.Digest
import Standards.NIST.SHA2.Preprocessing
import Standards.NIST.SHA2.Computation

/-!
# FIPS 180-4

The SHA-224, SHA-256, SHA-512, and SHA-384 constructions in FIPS 180-4, §§6.2–6.5, for messages
of fewer than 2^64 (SHA-224, SHA-256) or 2^128 bits (SHA-384, SHA-512), and SHA-256's `hashBytes`
of an octet string read most significant bit first. The definitions are total; padding encodes the
bit length modulo 2^64 or 2^128.

Source: https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf
-/

namespace Standards.NIST.SHA2

open SHA256 in
/-- Pads and hashes M, then concatenates H₀ through H₇ as the digest (FIPS 180-4, §6.2). -/
def SHA256 (M : Array Bool) : Digest 32 :=
  let H := hashComputation (parse (pad M)) «H⁽⁰⁾»
  Digest.ofBits (Vector.ofFn (n := 256) fun j =>
    (H[j.val / 32]'(by omega)).getMsbD (j.val % 32))

/-- SHA-256 of an octet string, read most significant bit first, as 32 octets -/
def SHA256.hashBytes (M : ByteArray) : ByteArray :=
  ⟨(SHA256 (bytesToBits M)).bytes.toArray⟩

open SHA512 in
/-- Pads and hashes M, then concatenates H₀ through H₇ as the digest (FIPS 180-4, §6.4). -/
def SHA512 (M : Array Bool) : Digest 64 :=
  let H := hashComputation (parse (pad M)) «H⁽⁰⁾»
  Digest.ofBits (Vector.ofFn (n := 512) fun j =>
    (H[j.val / 64]'(by omega)).getMsbD (j.val % 64))

/--
Hashes M as SHA-512 does from the SHA-384 initial hash value, then truncates the final hash value
to its left-most 384 bits, H₀ through H₅, as the digest (FIPS 180-4, §6.5).
-/
def SHA384 (M : Array Bool) : Digest 48 :=
  let H := SHA512.hashComputation (SHA512.parse (SHA512.pad M)) SHA384.«H⁽⁰⁾»
  Digest.ofBits (Vector.ofFn (n := 384) fun j =>
    (H[j.val / 64]'(by omega)).getMsbD (j.val % 64))

/--
Hashes M as SHA-256 does from the SHA-224 initial hash value, then truncates the final hash value
to its left-most 224 bits, H₀ through H₆, as the digest (FIPS 180-4, §6.3).
-/
def SHA224 (M : Array Bool) : Digest 28 :=
  let H := SHA256.hashComputation (SHA256.parse (SHA256.pad M)) SHA224.«H⁽⁰⁾»
  Digest.ofBits (Vector.ofFn (n := 224) fun j =>
    (H[j.val / 32]'(by omega)).getMsbD (j.val % 32))

end Standards.NIST.SHA2
