import P256.Spec.Functions

/-!
# The argument check and specification of each entry point with a theorem, by name

The tables of `Tests/Generated/` name each call by its entry point; this gives, for each of the 6
entry points with a theorem, what its slices must hold and its specification, the signer's within at
most 8 RFC 6979 candidates.
-/

namespace P256.Tests.Functions

open P256.Spec

/-- A specification's result: `some bytes` on success, `none` for the crate's failure -/
abbrev Model := Array ByteArray → Option (Option ByteArray)

private def searched (within : Nat → Option (Option ByteArray)) : Option (Option ByteArray) :=
  (List.range 8).findSome? fun attempts => within (attempts + 1)

/-- Every entry point with a theorem: its name, argument check and specification -/
def all : List (String × (Array ByteArray → Bool) × Model) := [
  ("publicKeyFromSec1Bytes", Functions.publicKeyFromSec1BytesArguments,
    fun inputs => some (Keys.publicKeyFromSec1 inputs)),
  ("signingKeyTrySign", Functions.signingKeyTrySignArguments,
    fun inputs => searched fun attempts => Ecdsa.signMessageWithin attempts inputs),
  ("verifyingKeyVerify", Functions.verifyingKeyVerifyArguments,
    fun inputs => some (Ecdsa.verifyMessage inputs)),
  ("signatureFromSlice", Functions.signatureFromSliceArguments,
    fun inputs => some (Ecdsa.signatureFromSlice inputs)),
  ("signingKeyGenerateFromRng", Functions.signingKeyGenerateFromRngArguments,
    fun inputs => some (some (Generate.generatedSigningKey inputs))),
  ("ecdhDiffieHellman", Functions.ecdhDiffieHellmanArguments,
    fun inputs => some (some (Ecdh.diffieHellman inputs)))]

/--
The specification of entry `name` on `inputs`: `some (some bytes)` on success, `some none` for the
crate's failure; `none` for an unknown name or a signature search that needs more than 8 candidates
-/
def model (name : String) (inputs : Array ByteArray) : Option (Option ByteArray) := do
  let (_, _, f) ← all.find? (·.1 == name)
  f inputs

/-- Whether `inputs` meet entry `name`'s argument premise; false for an unknown name -/
def admits (name : String) (inputs : Array ByteArray) : Bool :=
  match all.find? (·.1 == name) with
  | some (_, arguments, _) => arguments inputs
  | none => false

end P256.Tests.Functions
