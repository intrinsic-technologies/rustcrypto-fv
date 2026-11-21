import Standards.RFC.DeterministicSigning.Signing

/-!
# Deterministic signing with additional data

The variant of RFC 6979, §3.6 that adds additional data `k'` to the input of HMAC, "concatenated
after bits2octets(H(m))". With empty `k'` it is the procedure of §3.2 that `Nonce.initialState`
and `Signing.signWithin` define; candidates, rejection, and the retry loop are those of §3.2.

§3.6 prints the changed step d only,
`K = HMAC_K(V || 0x00 || int2octets(x) || bits2octets(h1) || k')`, and calls `k'` the "additional
input" of SP 800-90A's HMAC_DRBG. This definition also appends `k'` in step f,
`K = HMAC_K(V || 0x01 || int2octets(x) || bits2octets(h1) || k')`, as HMAC_DRBG's update with
additional input does and as RustCrypto's `rfc6979` crate implements; that reading of §3.6 is an
interpretation, not text of the RFC.

Source: https://www.rfc-editor.org/rfc/rfc6979#section-3.6
-/

set_option autoImplicit false

namespace Standards.RFC.DeterministicSigning.AdditionalData

/--
Nonce initialization with additional data (RFC 6979, §3.2, steps b–g, with the variant of §3.6)

Parameters: a hash function, its block and digest sizes in octets, and positive subgroup order
Input: private scalar `secret` in `1 ≤ secret < order`, message digest `digest`, and additional
data `extra`, the `k'` of §3.6
Output: initial HMAC state `(K, V)`

1. Set `V` to `digestBytes` octets of `0x01` and `K` to `digestBytes` octets of `0x00`
2. Set `seed = intToOctets(secret) || bitsToOctets(digest) || extra`
3. Step d: set `K = HMAC(K, V || 0x00 || seed)`; step e: `V = HMAC(K, V)`
4. Step f: set `K = HMAC(K, V || 0x01 || seed)`; step g: `V = HMAC(K, V)`
5. Return `(K, V)`

These are the steps of `Nonce.initialState` with `extra` appended to its seed.
-/
def initialState (hash : ByteArray → ByteArray) (blockBytes digestBytes order secret : Nat)
    (digest extra : ByteArray) : Nonce.State :=
  let mac := Standards.RFC.HMAC.hmac hash blockBytes
  let value : ByteArray := ⟨Array.replicate digestBytes 1⟩
  let key : ByteArray := ⟨Array.replicate digestBytes 0⟩
  let seed := Nonce.intToOctets order secret ++ Nonce.bitsToOctets order digest ++ extra
  let key := mac key (value ++ ⟨#[0]⟩ ++ seed)
  let value := mac key value
  let key := mac key (value ++ ⟨#[1]⟩ ++ seed)
  let value := mac key value
  ⟨key, value⟩

/--
The first successful signature within `attempts` nonce candidates from the state `initialState`
derives with additional data `extra`, as `Signing.signWithin` does without it (RFC 6979, §§3.2
and 3.6). `none` denotes search exhaustion.
-/
def signWithin {Signature : Type} (hash : ByteArray → ByteArray)
    (blockBytes digestBytes order : Nat) (signWithNonce : Nat → Option Signature)
    (secret : Nat) (digest extra : ByteArray) (attempts : Nat) : Option Signature :=
  Signing.signingAttempts hash blockBytes digestBytes order signWithNonce attempts
    (initialState hash blockBytes digestBytes order secret digest extra)

end Standards.RFC.DeterministicSigning.AdditionalData
