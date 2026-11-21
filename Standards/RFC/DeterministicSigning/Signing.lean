import Standards.RFC.DeterministicSigning.Nonce

/-!
# Deterministic signing attempts

The retry procedure from RFC 6979, §3.2. The caller supplies the hash parameters, subgroup order,
secret scalar, digest, and a signing operation. That operation returns `none` when a nonce must
be rejected (for example, because a signature component is zero). No DSA or elliptic-curve
implementation is selected here.

Source: https://www.rfc-editor.org/rfc/rfc6979.html
-/

set_option autoImplicit false

namespace Standards.RFC.DeterministicSigning.Signing

/--
Return the first successful signature within `attempts` nonce candidates (RFC 6979, §3.2, step h).
Reject candidates outside `1 ≤ k < order` before calling `signWithNonce`. After either a rejected
candidate or a failed signature, advance the HMAC state with `Nonce.reject`.
`none` denotes search exhaustion, not a signing error. Hash sizes and order must be positive,
and the hash must return `digestBytes` octets as required by the nonce procedures.
-/
def signingAttempts {Signature : Type} (hash : ByteArray → ByteArray)
    (blockBytes digestBytes order : Nat) (signWithNonce : Nat → Option Signature) :
    Nat → Nonce.State → Option Signature
  | 0, _ => none
  | attempts + 1, state =>
    let (nonce, next) := Nonce.candidate hash blockBytes digestBytes order state
    let signature := if 0 < nonce && nonce < order then signWithNonce nonce else none
    match signature with
    | some signature => some signature
    | none => signingAttempts hash blockBytes digestBytes order signWithNonce attempts
        (Nonce.reject hash blockBytes next)

/--
Initialize RFC 6979's nonce state and try at most `attempts` candidates. The caller supplies a
valid secret scalar and the message digest, along with a signing operation closed over those
inputs. `none` denotes search exhaustion.
-/
def signWithin {Signature : Type} (hash : ByteArray → ByteArray)
    (blockBytes digestBytes order : Nat) (signWithNonce : Nat → Option Signature)
    (secret : Nat) (digest : ByteArray) (attempts : Nat) : Option Signature :=
  signingAttempts hash blockBytes digestBytes order signWithNonce attempts
    (Nonce.initialState hash blockBytes digestBytes order secret digest)

end Standards.RFC.DeterministicSigning.Signing
