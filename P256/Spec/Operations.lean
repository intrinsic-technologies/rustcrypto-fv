import Standards.NIST.EllipticCurves
import Standards.NIST.SHA2
import Standards.SECG.ECC
import Standards.RFC.DeterministicSigning

/-!
# P-256 parameters

The choices every P-256 specification shares, as instances of the shared standards: the curve's
domain parameters, square roots modulo its prime, SHA-256 with its block and digest sizes, and the
fixed-width `r ‖ s` signature bytes.

Source: https://nvlpubs.nist.gov/nistpubs/SpecialPublications/NIST.SP.800-186.pdf
-/

set_option autoImplicit false

namespace P256.Spec.Operations

open Standards.SECG.ECC Standards.NIST.SHA2

/-! ## Parameters -/

/-- P-256 domain parameters (SP 800-186, §3.2.1.3) -/
abbrev domain := Standards.NIST.EllipticCurves.P256.domain

/-- Square roots modulo the P-256 prime, which is `3 mod 4` (SP 800-186, Appendix E.3) -/
abbrev sqrtMod := Standards.NIST.EllipticCurves.Field.sqrtMod3Mod4 domain.p

/-- SHA-256, the message hash and the RFC 6979 HMAC hash (FIPS 180-4, §6.2) -/
abbrev hash := SHA256.hashBytes

/-- SHA-256 block size in octets (FIPS 180-4, §1, Figure 1) -/
abbrev hashBlockBytes := 64

/-- SHA-256 digest size in octets (FIPS 180-4, §1, Figure 1) -/
abbrev hashDigestBytes := 32

/-! ## Encodings -/

/-- Fixed-width big-endian `r ‖ s` signature encoding (RFC 7518, §3.4) -/
def encodeSignature (signature : Nat × Nat) : ByteArray :=
  Encoding.natToOctets 32 signature.1 ++ Encoding.natToOctets 32 signature.2

end P256.Spec.Operations
