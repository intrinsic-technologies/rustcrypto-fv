import P256.Spec.Ecdh
import P256.Spec.Keys

/-!
# A signing key generated from the caller's random bytes

`Generate::generate_from_rng` for `SigningKey` (crypto-common 0.2.2 `src/generate.rs:17-20`, which
calls `try_generate_from_rng`, ecdsa 0.17.0 `src/signing.rs:134-138`) draws its secret scalar from
random bytes the caller supplies, one slice, which the wrapper's generator hands out in order
through rand_core 0.10.1's `UnwrapErr`, by rejection sampling
(`NonZeroScalar::try_generate_from_rng`): 32-byte big-endian candidates, kept when in `[1, n − 1]`
(`Ecdh.drawNonzeroScalar`). Enough random bytes to reach an accepted block
(`Ecdh.hasRandomNonZeroScalar`) is a premise of the call: `UnwrapErr` would panic if they ran
out, a limit of the wrapper's generator, not of the crate.

The `SigningKey` holds the secret scalar `d` and the `VerifyingKey` its constructor computes from
it, the public point `dG` (ecdsa 0.17.0 `src/signing.rs:64-74`; `From<NonZeroScalar>`,
`src/signing.rs:479-492`). The wrapper writes both (`generatedSigningKey`), so the theorem covers
the verifying key too.

Source: https://www.secg.org/sec1-v2.pdf
-/

set_option autoImplicit false

namespace P256.Spec.Generate

open Standards.SECG.ECC Operations Ecdh

/-- The value `draw` takes from the first slice; empty when the bytes run out first -/
def drawn (draw : ByteArray → Option ByteArray) (inputs : Array ByteArray) : ByteArray :=
  (draw (Arith.argument inputs 0)).getD ByteArray.empty

/--
`generate_from_rng` for `SigningKey`: the key's 32-byte scalar (`to_bytes`;
`Ecdh.drawNonzeroScalar`)
-/
def generatedNonZeroScalar (inputs : Array ByteArray) : ByteArray :=
  drawn (fun bytes => (drawNonzeroScalar bytes).map (Encoding.natToOctets 32)) inputs

/--
`generate_from_rng` for `SigningKey`: the whole `SigningKey`, as the wrapper writes it: its secret
scalar `generatedNonZeroScalar`, 32 bytes big-endian (`to_bytes`), then its verifying key, the
public key of that scalar, `dG` (SEC 1 v2.0 §3.2.1), in the 65-byte uncompressed SEC 1 encoding
(`verifying_key().to_sec1_point(false)`), the encoding `SecretKey::public_key`'s specification
writes (`Keys.publicKeyOfSecret`)
-/
def generatedSigningKey (inputs : Array ByteArray) : ByteArray :=
  generatedNonZeroScalar inputs ++ Keys.publicKeyOfSecret #[generatedNonZeroScalar inputs]

end P256.Spec.Generate
