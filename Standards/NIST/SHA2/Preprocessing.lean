import Standards.NIST.SHA2.Representation

/-!
# SHA-2 preprocessing

Padding, parsing, and initialization from FIPS 180-4, §§5.1, 5.2, and 5.3.2–5.3.5. SHA-224 and
SHA-384 pad and parse as SHA-256 and SHA-512 do, so those paddings and parsings serve both.
The message is a bit string, including the empty string and non-byte-aligned strings.

Source: https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf
-/

namespace Standards.NIST.SHA2

namespace SHA256

/--
Appends a one bit, zero padding, and the bit length mod 2^64 as a 64-bit big-endian word
(FIPS 180-4, §5.1.1).
-/
def pad (M : Array Bool) : Array Bool :=
  let ℓ := M.size
  let k := (448 + 512 - (ℓ + 1) % 512) % 512
  M ++ #[true] ++ Array.replicate k false ++ (wordToBits (BitVec.ofNat 64 ℓ)).toArray

/-- Parses complete 512-bit blocks into words in left-to-right order (FIPS 180-4, §5.2.1). -/
def parse (M : Array Bool) : Array (Vector (BitVec 32) 16) :=
  let N := M.size / 512
  Array.ofFn fun i : Fin N =>
    Vector.ofFn fun j : Fin 16 =>
      bitsToWord (Vector.ofFn fun n : Fin 32 =>
        M[512 * i.val + 32 * j.val + n.val]'(by
          have hi := i.isLt
          have hj := j.isLt
          have hn := n.isLt
          dsimp [N] at hi
          omega))

/-- The initial hash value «H⁽⁰⁾», with words indexed from zero (FIPS 180-4, §5.3.3). -/
def «H⁽⁰⁾» : Vector (BitVec 32) 8 :=
  #v[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
     0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

end SHA256

namespace SHA512

/--
Appends a one bit, zero padding, and the bit length mod 2^128 as a 128-bit big-endian word
(FIPS 180-4, §5.1.2).
-/
def pad (M : Array Bool) : Array Bool :=
  let ℓ := M.size
  let k := (896 + 1024 - (ℓ + 1) % 1024) % 1024
  M ++ #[true] ++ Array.replicate k false ++ (wordToBits (BitVec.ofNat 128 ℓ)).toArray

/-- Parses complete 1024-bit blocks into words in left-to-right order (FIPS 180-4, §5.2.2). -/
def parse (M : Array Bool) : Array (Vector (BitVec 64) 16) :=
  let N := M.size / 1024
  Array.ofFn fun i : Fin N =>
    Vector.ofFn fun j : Fin 16 =>
      bitsToWord (Vector.ofFn fun n : Fin 64 =>
        M[1024 * i.val + 64 * j.val + n.val]'(by
          have hi := i.isLt
          have hj := j.isLt
          have hn := n.isLt
          dsimp [N] at hi
          omega))

/-- The SHA-512 initial hash value «H⁽⁰⁾», words indexed from zero (FIPS 180-4, §5.3.5). -/
def «H⁽⁰⁾» : Vector (BitVec 64) 8 :=
  #v[0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
     0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179]

end SHA512

namespace SHA384

/-- The SHA-384 initial hash value «H⁽⁰⁾», words indexed from zero (FIPS 180-4, §5.3.4). -/
def «H⁽⁰⁾» : Vector (BitVec 64) 8 :=
  #v[0xcbbb9d5dc1059ed8, 0x629a292a367cd507, 0x9159015a3070dd17, 0x152fecd8f70e5939,
     0x67332667ffc00b31, 0x8eb44a8768581511, 0xdb0c2e0d64f98fa7, 0x47b5481dbefa4fa4]

end SHA384

namespace SHA224

/-- The SHA-224 initial hash value «H⁽⁰⁾», words indexed from zero (FIPS 180-4, §5.3.2). -/
def «H⁽⁰⁾» : Vector (BitVec 32) 8 :=
  #v[0xc1059ed8, 0x367cd507, 0x3070dd17, 0xf70e5939,
     0xffc00b31, 0x68581511, 0x64f98fa7, 0xbefa4fa4]

end SHA224

end Standards.NIST.SHA2
