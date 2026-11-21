import P256.Spec.Points

/-!
# P-256 key encodings

The encodings p256's keys are read and written in, as RustCrypto's crates implement them for P-256
(`elliptic-curve` 0.14.3, `ecdsa` 0.17.0, `sec1` 0.8.1), built on these standards:

* secret scalars: the 32-octet big-endian `d` with `1 ≤ d < n` (SEC 1 v2.0 §2.3.8 to read it,
  §3.2.1 for its range);
* SEC 1 points (SEC 1 v2.0 §§2.3.3–2.3.4): `00`, `02`/`03`, `04`, and the compact form
  `05 ‖ x`, RustCrypto's own, decoded as `Points.decodePoint` and `Points.decodePublicKey` state.

Source: https://www.secg.org/sec1-v2.pdf
-/

set_option autoImplicit false

namespace P256.Spec.Keys

open Standards.SECG.ECC

/-! ## Scalars and points -/

/--
The secret scalar of `SecretKey::from_bytes`: 32 octets, big-endian, with `1 ≤ d < n` (SEC 1 v2.0
§2.3.8 and §3.2.1, `Keys.decodeSecret`)
-/
def secretOfBytes (input : ByteArray) : Option Nat :=
  Standards.SECG.ECC.Keys.decodeSecret Operations.domain input

/-- The public point `dG` of the secret scalar `d` (SEC 1 v2.0 §3.2.1) -/
def publicPoint (d : Nat) : Curve.Point := Curve.scalarMul Operations.domain d Operations.domain.G

/-- The SEC 1 encoding of `point`, compressed or not; the identity is `00` (SEC 1 v2.0 §2.3.3) -/
def encodePoint (compressed : Bool) (point : Curve.Point) : ByteArray :=
  Points.encodePoint Operations.domain compressed point

end P256.Spec.Keys
