import Standards.SECG.ECC
import Standards.SECG.DomainParameters.Secp256k1
import Standards.NIST.EllipticCurves.Field

/-!
# k256's curve, keys and ECDH

The `Standards` definitions of SEC 1 instantiated at the secp256k1 parameters of SEC 2, as the
`k256` 0.14.0 crate uses them: secret keys (SEC 1 v2.0, §3.2.1), public keys and their SEC 1
encodings (§§2.3.3–2.3.4), raw ECDH (§3.3.1), and key generation from a caller's random bytes. Each
definition says where the crate goes beyond the standard: the compact point form `05 ‖ x`, the
33-byte `GroupEncoding` of the identity, ECDH with the identity, and the rejection sampling of
`SigningKey::generate_from_rng`.

Source: https://www.secg.org/sec1-v2.pdf
-/

set_option autoImplicit false

namespace K256.Spec.Secp256k1

open Standards.SECG.ECC Standards.SECG.DomainParameters

/--
Square root modulo the secp256k1 prime, which is `3 mod 4`, or `none` for a non-residue
(SP 800-186, Appendix E.3)
-/
def sqrtMod (value : Nat) : Option Nat :=
  Standards.NIST.EllipticCurves.Field.sqrtMod3Mod4 Secp256k1.domain.p value

/--
A public key as `k256` decodes it (`PublicKey::from_sec1_bytes`): a SEC 1 compressed or
uncompressed encoding of a point other than the identity (SEC 1 v2.0, §§2.3.4 and 3.2.2.1), or the
33-byte compact encoding, the octet `0x05` followed by `x`, of the point with x-coordinate `x` and
an even y-coordinate.

The compact form is not SEC 1, which defines no `0x05` tag: it is RustCrypto's `sec1` crate's
variant (`Tag::Compact`, sec1 0.8.1 `src/point.rs`), which `k256` decodes with BIP 340's even-`y`
rule (`DecompactPoint` for `AffinePoint`, `src/arithmetic/affine.rs:283-287`, called at `:331`).
This definition states what the crate does. `groupPoint` reads 33-byte inputs through this
definition, so the same holds for `GroupEncoding::from_bytes`.
-/
def decodePublicKey (input : ByteArray) : Option Curve.Point :=
  let encoding := if input.size == 33 && input.data[0]? == some 5 then
    ⟨#[2]⟩ ++ input.extract 1 33
  else input
  Points.decodePublicKey Secp256k1.domain sqrtMod encoding

/--
The point `GroupEncoding::from_bytes` decodes from 33 bytes (`src/arithmetic/affine.rs:292-307`):
the identity for 33 zero bytes, otherwise a public key encoding of that length as
`decodePublicKey` reads it (compressed SEC 1 or compact); `none` for anything else
-/
def groupPoint (input : ByteArray) : Option Curve.Point :=
  if input == ⟨Array.replicate 33 0⟩ then some .infinity
  else if input.size == 33 then decodePublicKey input else none

/--
The secret scalar `SigningKey::generate_from_rng` draws from the caller's random bytes, taken in
order in 32-byte blocks: the first block that is the big-endian encoding of a scalar `d` with
`1 ≤ d < n` (SEC 1 v2.0, Appendix C.4, `Keys.decodeSecret`), or `none` if no whole block is.

This is the crate's rejection sampling (`Field::try_random` for `Scalar`,
`src/arithmetic/scalar.rs:199-218`, which redraws a block encoding `n` or more, inside
`NonZeroScalar::try_generate_from_rng`, which redraws a zero scalar): SEC 1 §3.2.1 only asks for a
random `d` in `[1, n − 1]`, which this draw gives.
-/
def randomSecret (random : ByteArray) : Option Nat :=
  (List.range (random.size / 32)).findSome? fun block =>
    Keys.decodeSecret Secp256k1.domain (random.extract (32 * block) (32 * block + 32))

/--
The 65-byte uncompressed SEC 1 encoding (SEC 1 v2.0, §2.3.3) of the public key `d · G` of a
32-byte big-endian secret scalar (§3.2.1), empty for a secret outside `1 ≤ d < n`
-/
def publicKeyOf (secret : ByteArray) : ByteArray :=
  ((Keys.publicKey Secp256k1.domain secret).map (Points.encodePoint Secp256k1.domain false)).getD
    ByteArray.empty

/--
The whole `SigningKey` that `SigningKey::generate_from_rng` gives for the caller's random bytes, as
the wrapper writes it, 97 bytes. A `SigningKey` holds two values (ecdsa 0.17.0
`src/signing.rs:64-74`): the secret scalar `d` and the `VerifyingKey` its constructor computes from
it, the public point `d · G` (`From<NonZeroScalar>`, `src/signing.rs:479-492`, through
`PublicKey::from_secret_scalar`). So this is the scalar `randomSecret` draws, 32 bytes big-endian
(`SigningKey::to_bytes`), then its public key `d · G` (SEC 1 v2.0, §3.2.1) in the 65-byte
uncompressed SEC 1 encoding (`verifying_key().to_sec1_point(false)`), as `publicKeyOf` gives it.
Empty when no whole block is a valid scalar, which `ValidCall` excludes.
-/
def generatedSigningKey (random : ByteArray) : ByteArray :=
  match randomSecret random with
  | some secret =>
    Encoding.natToOctets 32 secret ++ publicKeyOf (Encoding.natToOctets 32 secret)
  | none => ByteArray.empty

/--
The 32 bytes `ecdh::diffie_hellman` gives for a 32-byte big-endian secret scalar `d` and a point
`Q`, given as its 33-byte `GroupEncoding` (`groupPoint`): for `Q` other than the identity, raw ECDH
(SEC 1 v2.0, §3.3.1), the big-endian x-coordinate of `d · Q`; for the identity, 32 zero bytes, the
x-coordinate field of k256's `AffinePoint::IDENTITY` (`src/arithmetic/affine.rs:53-57`), which
`SharedSecret::new` copies out (elliptic-curve 0.14.3, `src/ecdh.rs:61-71` and `187-194`); empty
if the bytes do not decode.

SEC 1 §3.3.1 takes only a valid public key, which the identity is not (§3.2.2.1); `diffie_hellman`
takes any `AffinePoint` and cannot fail, so the crate's result is stated for the identity.
-/
def sharedSecret (secret publicKey : ByteArray) : ByteArray :=
  match groupPoint publicKey with
  | some .infinity => ⟨Array.replicate 32 0⟩
  | some point => (Keys.sharedSecret Secp256k1.domain secret point).getD ByteArray.empty
  | none => ByteArray.empty

end K256.Spec.Secp256k1
