/-!
# Digest

Digests as bytes, and the conversions between byte strings and the bit strings of FIPS 202:
byte `i` holds bits `8i` through `8i + 7`, least significant bit first (FIPS 202, Appendix B.1).

Source: https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.202.pdf
-/

namespace Standards.NIST.SHA3

/-- A digest of `byteCount` bytes, in address order -/
abbrev Digest (byteCount : Nat) := Vector UInt8 byteCount

namespace Digest

variable {byteCount : Nat}

/-- Returns the digest bytes in order -/
def toBytes (digest : Digest byteCount) : ByteArray :=
  ⟨digest.toArray⟩

/-- Packs bits into digest bytes, each group of eight least significant bit first, in order -/
def ofBits (bits : Vector Bool (8 * byteCount)) : Digest byteCount :=
  Vector.ofFn fun i =>
    let byteBits := List.ofFn fun j : Fin 8 => bits[8 * i.val + j.val]'(by omega)
    UInt8.ofBitVec ((BitVec.ofBoolListLE byteBits).cast (by simp [byteBits]))

end Digest

/-- Flattens a byte array into bits, least significant bit first within each byte, in byte order -/
def bytesToBits (bytes : ByteArray) : Array Bool :=
  bytes.data.flatMap fun byte => (Array.range 8).map byte.toBitVec.getLsbD

end Standards.NIST.SHA3
