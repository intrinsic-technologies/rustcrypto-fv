import Standards.NIST.SHA1

/-!
# The `sha1` 0.11.0 hash value in memory

The byte layout of the `[u32; 5]` hash value that `block_api::compress` reads and overwrites.
FIPS 180-4 defines the five words, not their bytes in memory; this follows the crate's source:

* `sha1` 0.11.0, `src/block_api.rs`:
  https://github.com/RustCrypto/hashes/blob/sha1-v0.11.0/sha1/src/block_api.rs

The hash computation itself is FIPS 180-4's SHA-1 in `Standards.NIST.SHA1`:
https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf

Only the call semantics of `sha1_compress` in `Sha1.Spec.Program` use this layout. The theorems in
`Sha1.Statements` state the FIPS 180-4 digest directly, with no crate specification in between.
-/

namespace Sha1.Spec.Hasher

open Standards.NIST

/--
The bytes of a `[u32; 5]` hash value as it lies in memory: `H[0]` to `H[4]`, each least
significant byte first, as x86-64 stores a `u32`.
-/
def stateBytes (H : Vector (BitVec 32) 5) : Vector UInt8 20 :=
  Vector.ofFn fun i =>
    UInt8.ofBitVec ((H[i.val / 4]'(by omega) >>> (8 * (i.val % 4))).setWidth 8)

end Sha1.Spec.Hasher
