import P256.Spec.Points

/-!
# P-256 ECDH

`ecdh::diffie_hellman` of elliptic-curve 0.14.3 `src/ecdh.rs` at `NistP256`: raw ECDH, the
x-coordinate of `dQ` with no key derivation (SEC 1 v2.0, §3.3.1); and the draw of a nonzero
scalar from the caller's random bytes, which `SigningKey::generate_from_rng` makes
(`Generate.lean`).

Arguments are the bytes of the crate's types (`program/src/extras.rs`): a scalar is 32 bytes
big-endian (SEC 1 v2.0, §2.3.8), a point SEC 1 bytes (§2.3.4) that the crate's decoder accepts
(`P256.Spec.Points.decodePoint`), the compact `05 ‖ x` included. That the bytes are such values is
a premise of the call (`Arith.isNonZeroScalar`, `Points.isAffineEncoding`), as are enough random
bytes to reach an accepted candidate (`hasRandomNonZeroScalar`): running out is a limit of the
wrapper's generator, not of the crate.

Source: https://www.secg.org/sec1-v2.pdf
-/

set_option autoImplicit false

namespace P256.Spec.Ecdh

open Standards.SECG.ECC Operations

/--
The first of the consecutive `width`-byte blocks of `bytes` that `accept` maps to a value, or
`none` if the blocks run out first, a shorter tail included: how the crate's rejection-sampling
loops draw from a random-number generator that hands out the caller's bytes in order and fails
on a request for more than remain
-/
def firstAccepted {α : Type} (width : Nat) (accept : ByteArray → Option α) (bytes : ByteArray) :
    Option α := go (bytes.size + 1) 0
where
  /-- Blocks from `offset` on, with `fuel` more than the blocks that remain -/
  go : Nat → Nat → Option α
    | 0, _ => none
    | fuel + 1, offset =>
      if offset + width ≤ bytes.size then
        match accept (bytes.extract offset (offset + width)) with
        | some value => some value
        | none => go fuel (offset + width)
      else none

/--
A nonzero scalar drawn from the random bytes `bytes` (`NonZeroScalar::try_generate_from_rng`,
elliptic-curve 0.14.3 `src/scalar/nonzero.rs`): 32-byte big-endian candidates, read as
`Scalar::try_random` reads them, taken until one is a secret scalar in `1 ≤ d < n`, SEC 1's
check (`Keys.decodeSecret`, SEC 1 v2.0, §3.2.1); the crate adds the draw loop
-/
def drawNonzeroScalar (bytes : ByteArray) : Option Nat :=
  firstAccepted 32 (Keys.decodeSecret domain) bytes

/--
Whether random bytes, the first slice, hold a block that `drawNonzeroScalar` accepts: the premise
of `SigningKey::generate_from_rng`'s call
-/
def hasRandomNonZeroScalar (inputs : Array ByteArray) : Bool :=
  (drawNonzeroScalar (Arith.argument inputs 0)).isSome

/--
The x-coordinate of `dQ`, 32 bytes big-endian (`SharedSecret::raw_secret_bytes`, SEC 1 v2.0,
§3.3.1). For the identity, which `diffie_hellman` admits, the crate gives 32 zero bytes, the
x-coordinate p256 stores for the identity; SEC 1 §3.3.1 outputs "invalid" there, and the crate's
docs do not describe the case (`P256/README.md`, Deliberate differences from the standards)
-/
def sharedX (d : Nat) (point : Curve.Point) : ByteArray := Points.xBytes (Points.mul d point)

/--
`ecdh::diffie_hellman(secret, public)`: a nonzero scalar and any point, the identity included; the
32-byte shared x-coordinate (`sharedX`)
-/
def diffieHellman (inputs : Array ByteArray) : ByteArray :=
  sharedX (Points.scalarArgument inputs 0) (Points.pointArgument inputs 1)

end P256.Spec.Ecdh
