import P256.Spec.Program
import P256.Spec.Functions

/-!
# The entry points

Each one-function entry point's routine under `P256.Spec.Program.Routines`, the namespace of their
one contract (`Spec/Program.lean`): its address, its stack budget, its argument premise, which
arguments its function accepts, its output register (RCX in every wrapper), its result's size and
its heap bound. The stack budget is the extraction's estimate where it has one; otherwise it is the
deepest returning call path in the disassembly of `.text`, plus the same 128 bytes of slack as the
extraction's estimates; each doc names the functions with the largest frames on that path. The
extraction has no estimate for any function with a theorem: its estimator stops at a call through a
register (here only calls to `memcpy`) or at a backward branch it reads as a stack allocation in a
loop (here only branches around arguments pushed for one call and popped after it). A path's depth
counts each function's `push`es and `sub rsp`, and each call's callee depth and 8-byte return
address; calls to functions that never return (the panic functions, `abi::outside`, the
allocation-failure handlers) are on no returning path. The budgets are constant: variable-length
inputs and results live in the caller's buffers and heap, and no loop allocates stack. A heap bound
is 0 for a function that allocates nothing; the others bound what the call allocates.
-/

set_option autoImplicit false

namespace P256.Spec.Program.Routines

open P256.Spec

/--
The wrapper `p256_public_key_from_sec1_bytes`, calling `PublicKey::from_sec1_bytes`, which writes
the public key's 65 uncompressed bytes after their length. The extraction gives no stack estimate
(`Extracted/Symbols.lean`); the budget is the deepest returning call path in the disassembly, 3,920
bytes below entry RSP, through `PublicKey::from_sec1_bytes`, the point decompression,
`FieldElement::sqrt` and `pow_montgomery_form` (a 1,416-byte frame), plus 128 bytes of slack, 4,048
bytes. It allocates nothing.
-/
def publicKeyFromSec1Bytes : Routine where
  entryAddress := Extracted.publicKeyFromSec1BytesAddress
  minStackBytes := 4048
  arguments := Functions.publicKeyFromSec1BytesArguments
  accepts := fun inputs => (Keys.publicKeyFromSec1 inputs).isSome
  outputPointer := .rcx
  outputBytes := fun inputs => resultBytes (Keys.publicKeyFromSec1 inputs)
  heapBytes := fun _ => 0

/--
The wrapper `p256_projective_point_add`, calling `ProjectivePoint::add`, which writes the sum's SEC
1 encoding, 65 bytes or the identity's 1, after its length. The extraction gives no stack estimate
(`Extracted/Symbols.lean`); the budget is the deepest returning call path in the disassembly, 4,576
bytes below entry RSP, through the wrapper's operand decoding, the point decompression,
`FieldElement::sqrt` and `pow_montgomery_form` (a 1,416-byte frame), plus 128 bytes of slack, 4,704
bytes. It allocates nothing.
-/
def projectivePointAdd : Routine where
  entryAddress := Extracted.projectivePointAddAddress
  minStackBytes := 4704
  arguments := Functions.projectivePointAddArguments
  accepts := fun _ => true
  outputPointer := .rcx
  outputBytes := fun inputs => (Points.pointAdd inputs).size
  heapBytes := fun _ => 0

/--
The wrapper `p256_signing_key_try_sign`, calling `Signer::try_sign` for `SigningKey` at `Signature`,
which writes the signature `r ‖ s`, 64 bytes, after its length. The extraction gives no stack
estimate (`Extracted/Symbols.lean`); the budget is the deepest returning call path in the
disassembly, 4,984 bytes below entry RSP, through `sign_prehashed_rfc6979` (a 2,296-byte frame), RFC
6979's `KGenerator::fill_next_k`, `HmacDrbg::fill_bytes`, `update` and `update_v`, HMAC's
finalization (`SimpleHmac`'s `finalize_into`) and `compress256`, plus 128 bytes of slack, 5,112
bytes. It allocates nothing.
-/
def signingKeyTrySign : Routine where
  entryAddress := Extracted.signingKeyTrySignAddress
  minStackBytes := 5112
  arguments := Functions.signingKeyTrySignArguments
  accepts := fun _ => true
  outputPointer := .rcx
  outputBytes := fun _ => Ecdsa.signatureBytes
  heapBytes := fun _ => 0

/--
The wrapper `p256_verifying_key_verify`, calling `Verifier<Signature>::verify` for `VerifyingKey`,
which writes only the length 0 for a valid signature. The extraction gives no stack estimate
(`Extracted/Symbols.lean`); the budget is the deepest returning call path in the disassembly,
10,152 bytes below entry RSP, through `DigestVerifier::verify_digest`, into which
`verify_prehashed` is inlined, and `ProjectivePoint`'s linear combination (a 6,552-byte frame), its
point table, a point doubling and a field squaring, plus 128 bytes of slack, 10,280 bytes. It
allocates nothing.
-/
def verifyingKeyVerify : Routine where
  entryAddress := Extracted.verifyingKeyVerifyAddress
  minStackBytes := 10280
  arguments := Functions.verifyingKeyVerifyArguments
  accepts := fun inputs => (Ecdsa.verifyMessage inputs).isSome
  outputPointer := .rcx
  outputBytes := fun inputs => resultBytes (Ecdsa.verifyMessage inputs)
  heapBytes := fun _ => 0

/--
The wrapper `p256_signature_from_slice`, calling `Signature::from_slice`, which writes the signature
`r ‖ s`, 64 bytes, after its length. The extraction gives no stack estimate
(`Extracted/Symbols.lean`); the budget is the deepest returning call path in the disassembly, 528
bytes below entry RSP, through `Signature::from_slice`, `ScalarValue::from_slice` and
`fill_limbs_from_be_slice_truncated`, plus 128 bytes of slack, 656 bytes. It allocates nothing.
-/
def signatureFromSlice : Routine where
  entryAddress := Extracted.signatureFromSliceAddress
  minStackBytes := 656
  arguments := Functions.signatureFromSliceArguments
  accepts := fun inputs => (Ecdsa.signatureFromSlice inputs).isSome
  outputPointer := .rcx
  outputBytes := fun inputs => resultBytes (Ecdsa.signatureFromSlice inputs)
  heapBytes := fun _ => 0

/--
The wrapper `p256_signing_key_generate_from_rng`, calling `Generate::generate_from_rng` for
`SigningKey`, which writes the key's secret scalar, 32 bytes, then its verifying key, 65
uncompressed bytes, after their length. The extraction gives no stack estimate
(`Extracted/Symbols.lean`); the budget is the deepest returning call path in the disassembly, 3,896
bytes below entry RSP, through `SigningKey`'s `try_generate_from_rng`,
`PublicKey::from_secret_scalar`, which makes the key's public point (a 1,944-byte frame, the scalar
multiplication `ProjectivePoint * &Scalar` inlined), `lincomb`, a point doubling and a field
squaring, plus 128 bytes of slack, 4,024 bytes. It allocates nothing.
-/
def signingKeyGenerateFromRng : Routine where
  entryAddress := Extracted.signingKeyGenerateFromRngAddress
  minStackBytes := 4024
  arguments := Functions.signingKeyGenerateFromRngArguments
  accepts := fun _ => true
  outputPointer := .rcx
  outputBytes := fun inputs => (Generate.generatedSigningKey inputs).size
  heapBytes := fun _ => 0

/--
The wrapper `p256_ecdh_diffie_hellman`, calling `ecdh::diffie_hellman`, which writes the shared
secret's 32 bytes after their length. The extraction gives no stack estimate
(`Extracted/Symbols.lean`); the budget is the deepest returning call path in the disassembly, 3,976
bytes below entry RSP, through `diffie_hellman` (a 2,056-byte frame, the scalar multiplication
`ProjectivePoint * &Scalar` inlined), `lincomb`, a point doubling and a field squaring, plus 128
bytes of slack, 4,104 bytes. It allocates nothing.
-/
def ecdhDiffieHellman : Routine where
  entryAddress := Extracted.ecdhDiffieHellmanAddress
  minStackBytes := 4104
  arguments := Functions.ecdhDiffieHellmanArguments
  accepts := fun _ => true
  outputPointer := .rcx
  outputBytes := fun inputs => (Ecdh.diffieHellman inputs).size
  heapBytes := fun _ => 0

end P256.Spec.Program.Routines
