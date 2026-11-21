import Standards.NIST.SHA2.Hash

/-!
# SHA-512/224 and SHA-512/256

The SHA-512/t truncated hash functions of FIPS 180-4: the SHA-512/224 and SHA-512/256 initial hash
values (§§5.3.6.1 and 5.3.6.2), and SHA-512/224 and SHA-512/256 themselves (§§6.6 and 6.7). Each
hashes as SHA-512 does from its own initial hash value, then keeps the left-most bits of the final
hash value. SHA-224 (§§5.3.2 and 6.3) is defined in `Standards.NIST.SHA2.Preprocessing` and
`Standards.NIST.SHA2.Hash`. The initial hash values are transcribed from the standard, which prints
each as eight upper-case hex words, so search for `8C3D37C819544DA2` or `22312194FC2BF72C`.

Source: https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf
-/

namespace Standards.NIST.SHA2

namespace SHA512_224

/-- The SHA-512/224 initial hash value «H⁽⁰⁾», words indexed from zero (FIPS 180-4, §5.3.6.1). -/
def «H⁽⁰⁾» : Vector (BitVec 64) 8 :=
  #v[0x8C3D37C819544DA2, 0x73E1996689DCD4D6, 0x1DFAB7AE32FF9C82, 0x679DD514582F9FCF,
     0x0F6D2B697BD44DA8, 0x77E36F7304C48942, 0x3F9D85A86A1D36C8, 0x1112E6AD91D692A1]

end SHA512_224

namespace SHA512_256

/-- The SHA-512/256 initial hash value «H⁽⁰⁾», words indexed from zero (FIPS 180-4, §5.3.6.2). -/
def «H⁽⁰⁾» : Vector (BitVec 64) 8 :=
  #v[0x22312194FC2BF72C, 0x9F555FA3C84C64C2, 0x2393B86B6F53B151, 0x963877195940EABD,
     0x96283EE2A88EFFE3, 0xBE5E1E2553863992, 0x2B0199FC2C85B8AA, 0x0EB72DDC81C52CA2]

end SHA512_256

/--
Hashes M as SHA-512 does from the SHA-512/224 initial hash value, then truncates the final hash
value to its left-most 224 bits as the digest (FIPS 180-4, §6.6).
-/
def SHA512_224 (M : Array Bool) : Digest 28 :=
  let H := SHA512.hashComputation (SHA512.parse (SHA512.pad M)) SHA512_224.«H⁽⁰⁾»
  Digest.ofBits (Vector.ofFn (n := 224) fun j =>
    (H[j.val / 64]'(by omega)).getMsbD (j.val % 64))

/--
Hashes M as SHA-512 does from the SHA-512/256 initial hash value, then truncates the final hash
value to its left-most 256 bits, H₀ through H₃, as the digest (FIPS 180-4, §6.7).
-/
def SHA512_256 (M : Array Bool) : Digest 32 :=
  let H := SHA512.hashComputation (SHA512.parse (SHA512.pad M)) SHA512_256.«H⁽⁰⁾»
  Digest.ofBits (Vector.ofFn (n := 256) fun j =>
    (H[j.val / 64]'(by omega)).getMsbD (j.val % 64))

end Standards.NIST.SHA2
