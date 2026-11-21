/-!
# Hash-based message authentication

HMAC from RFC 2104, §2, parameterized by the hash function and block size.

Source: https://www.rfc-editor.org/rfc/rfc2104.html
-/

set_option autoImplicit false

namespace Standards.RFC.HMAC

/--
HMAC (RFC 2104, §2)

Parameters: a hash function and its block size `B` in octets; the digest fits in one block
Input: key `K` and message `input`
Output: the message authentication code

1. If `K` is longer than `B` octets, replace it with its hash
2. Pad `K` with zero octets to length `B`
3. Set `inner = K XOR ipad` and `outer = K XOR opad`, where `ipad` and `opad` are `B` repetitions of
   `0x36` and `0x5c`, respectively
4. Return `hash(outer || hash(inner || input))`
-/
def hmac (hash : ByteArray → ByteArray) (blockBytes : Nat)
    (key input : ByteArray) : ByteArray :=
  let key := if key.size > blockBytes then hash key else key
  let inner : ByteArray := ⟨(Array.range blockBytes).map fun i => key.data[i]?.getD 0 ^^^ 0x36⟩
  let outer : ByteArray := ⟨(Array.range blockBytes).map fun i => key.data[i]?.getD 0 ^^^ 0x5c⟩
  hash (outer ++ hash (inner ++ input))

end Standards.RFC.HMAC
