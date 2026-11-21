import P256.Spec.Operations
import Standards.NIST.EllipticCurves.Field
import Standards.RFC.BaseEncodings

/-!
# Byte forms and argument checks shared by the P-256 specifications

The byte forms the wrappers read and write, and what a slice must hold to be a value of its Rust
argument. Elements of the scalar field GF(n) are natural numbers below the modulus (SP 800-186,
§3.1.2, whose arithmetic `Standards.NIST.EllipticCurves.Field` defines), written as 32 big-endian
octets (SEC 1 v2.0, §2.3.5).

Byte forms chosen here: a `U256` is 32 big-endian bytes. The wrappers check none of this: what a
slice must hold to be a value of its Rust argument is a premise of the call (`Spec/Program.lean`,
`ValidCall`), stated per entry point with the checks below (`slices`, `anyBytes`,
`isNonZeroScalar`). The decoders below read any bytes, so every specification is total; on the
slices a call admits they give the argument's value.

Source: https://nvlpubs.nist.gov/nistpubs/SpecialPublications/NIST.SP.800-186.pdf
-/

set_option autoImplicit false

namespace P256.Spec.Arith

open Standards.SECG.ECC Operations

/-- The bytes as an unsigned big-endian integer (SEC 1 v2.0, §2.3.8) -/
def decodeBigEndian (bytes : ByteArray) : Nat := Encoding.octetsToNat bytes

/-- An element argument of GF(`modulus`): its 32 bytes read big-endian -/
def element (_modulus : Nat) (bytes : ByteArray) : Nat := decodeBigEndian bytes

/-- A `U256` argument: its 32 bytes read big-endian -/
def uint (bytes : ByteArray) : Nat := decodeBigEndian bytes

/-- The bytes of slice `i`, empty past the last slice (`ValidCall` supplies every slice it reads) -/
def argument (inputs : Array ByteArray) (i : Nat) : ByteArray := inputs.getD i .empty

/-! ## What a slice must hold: the premises of `ValidCall` -/

/--
The slices are as many as `checks`, and slice `i` passes check `i`: the argument premise of an
entry point with a fixed number of slices
-/
def slices (checks : List (ByteArray → Bool)) (inputs : Array ByteArray) : Bool :=
  inputs.size == checks.length && (inputs.toList.zip checks).all fun (bytes, check) => check bytes

/-- Any bytes: a `&[u8]` argument -/
def anyBytes (_bytes : ByteArray) : Bool := true

/--
A nonzero scalar or secret key: SEC 1's secret-key check, `1 ≤ d < n` on 32 big-endian bytes
(`Standards.SECG.ECC.Keys.decodeSecret`, SEC 1 v2.0, §3.2.1), which `SecretKey::from_bytes`,
`SigningKey::from_bytes` and `NonZeroScalar::from_repr` make
-/
def isNonZeroScalar (bytes : ByteArray) : Bool := (Keys.decodeSecret Operations.domain bytes).isSome

end P256.Spec.Arith
