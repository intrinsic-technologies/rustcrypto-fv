import Standards.RFC.HMAC.Basic

/-!
# Deterministic DSA and ECDSA nonces

Integer conversions and HMAC state transitions from RFC 6979, §§2.3 and 3.2. A candidate is accepted
when it lies in `1 ≤ k < order` and gives nonzero `r` (§3.4) and `s` (SEC 1 v2.0, §4.1.3);
rejection advances the state before the next attempt.

Source: https://www.rfc-editor.org/rfc/rfc6979.html
-/

set_option autoImplicit false

namespace Standards.RFC.DeterministicSigning.Nonce

/-- Bit length `qlen` of a positive subgroup order (RFC 6979, §2.3) -/
def orderBits (order : Nat) : Nat := order.log2 + 1

/--
Interpret up to the leftmost `qlen` bits as a big-endian integer, for positive `order` (RFC 6979,
§2.3.2).
-/
def bitsToInt (order : Nat) (input : ByteArray) : Nat :=
  (input.data.foldl (fun value byte => 256 * value + byte.toNat) 0) / 2 ^ (8 * input.size - orderBits order)

/--
Encode `0 ≤ value < order` in `⌈qlen / 8⌉` big-endian octets, for positive `order` (RFC 6979,
§2.3.3).
-/
def intToOctets (order value : Nat) : ByteArray :=
  let length := (orderBits order + 7) / 8
  ⟨(Array.range length).map fun i => UInt8.ofNat (value / 256 ^ (length - 1 - i) % 256)⟩

/--
Truncate to `qlen` bits, reduce modulo positive `order`, and encode in `⌈qlen / 8⌉` big-endian
octets (RFC 6979, §2.3.4).
-/
def bitsToOctets (order : Nat) (input : ByteArray) : ByteArray :=
  intToOctets order (bitsToInt order input % order)

/-- HMAC key `K` and chaining value `V` (RFC 6979, §3.2) -/
structure State where
  key : ByteArray
  value : ByteArray

/--
Deterministic nonce initialization (RFC 6979, §3.2, steps b–g)

Parameters: a hash function, its block and digest sizes in octets, and positive subgroup order
Input: private scalar `secret` in `1 ≤ secret < order` and message digest `digest`
Output: initial HMAC state `(K, V)`

1. Set `V` to `digestBytes` octets of `0x01` and `K` to `digestBytes` octets of `0x00`
2. Set `seed = intToOctets(secret) || bitsToOctets(digest)`
3. Set `K = HMAC(K, V || 0x00 || seed)`, then `V = HMAC(K, V)`
4. Set `K = HMAC(K, V || 0x01 || seed)`, then `V = HMAC(K, V)`
5. Return `(K, V)`

The digest is supplied by the caller; no extra entropy or personalization is included.
-/
def initialState (hash : ByteArray → ByteArray) (blockBytes digestBytes order secret : Nat)
    (digest : ByteArray) : State :=
  let mac := Standards.RFC.HMAC.hmac hash blockBytes
  let value : ByteArray := ⟨Array.replicate digestBytes 1⟩
  let key : ByteArray := ⟨Array.replicate digestBytes 0⟩
  let seed := intToOctets order secret ++ bitsToOctets order digest
  let key := mac key (value ++ ⟨#[0]⟩ ++ seed)
  let value := mac key value
  let key := mac key (value ++ ⟨#[1]⟩ ++ seed)
  let value := mac key value
  ⟨key, value⟩

/--
Deterministic nonce candidate (RFC 6979, §3.2, steps h.1–h.3)

Parameters: a hash function, its block size, positive digest size, and positive subgroup order
Input: HMAC state `(K, V)`
Output: candidate integer `k` and updated state

1. Initialize an empty octet string `T`
2. Repeatedly set `V = HMAC(K, V)` and append `V` to `T` until `T` contains at least `qlen` bits
3. Set `k = bitsToInt(T)` and return `(k, (K, V))`

The caller checks `1 ≤ k < order` and uses `reject` before retrying a rejected candidate.
-/
def candidate (hash : ByteArray → ByteArray) (blockBytes digestBytes order : Nat)
    (state : State) : Nat × State := Id.run do
  let mut value := state.value
  let mut collected := ByteArray.empty
  for _ in [:(orderBits order + 8 * digestBytes - 1) / (8 * digestBytes)] do
    value := Standards.RFC.HMAC.hmac hash blockBytes state.key value
    collected := collected ++ value
  return (bitsToInt order collected, ⟨state.key, value⟩)

/-- Advance the HMAC state after a rejected nonce (RFC 6979, §3.2, step h.3). -/
def reject (hash : ByteArray → ByteArray) (blockBytes : Nat) (state : State) : State :=
  let key := Standards.RFC.HMAC.hmac hash blockBytes state.key (state.value ++ ⟨#[0]⟩)
  ⟨key, Standards.RFC.HMAC.hmac hash blockBytes key state.value⟩

end Standards.RFC.DeterministicSigning.Nonce
