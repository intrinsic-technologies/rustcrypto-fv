import Standards.NIST.SHA2.Representation

/-!
# Message digests

A message digest as bytes in address order, with its packing from bits, each byte read most
significant bit first as FIPS 180-4, §3.1, orders bits. The SHA-1 and SHA-2 definitions return
their digests in this form.

Source: https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf
-/

namespace Standards.NIST.SHA2

/-- A message digest as `byteCount` bytes in address order. -/
structure Digest (byteCount : Nat) where
  /-- The digest bytes in address order. -/
  bytes : Vector UInt8 byteCount
  deriving DecidableEq, Repr

namespace Digest

/-- Packs bits into a digest, reading each group of eight most significant bit first. -/
def ofBits {byteCount : Nat} (bits : Vector Bool (8 * byteCount)) : Digest byteCount :=
  ⟨Vector.ofFn fun j =>
    UInt8.ofBitVec (bitsToWord (Vector.ofFn fun n : Fin 8 => bits[8 * j.val + n.val]'(by omega)))⟩

end Digest

end Standards.NIST.SHA2
