/-!
# The MD buffer

Step 3 of RFC 1321, §3.3: the four-word buffer (A, B, C, D) and its initial value.

Source: https://www.rfc-editor.org/rfc/rfc1321
-/

namespace Standards.RFC.MD5

/-- The four-word MD buffer (A, B, C, D), each a 32-bit register (RFC 1321, §3.3) -/
structure Buffer where
  A : BitVec 32
  B : BitVec 32
  C : BitVec 32
  D : BitVec 32
  deriving DecidableEq, Repr

/--
The initial buffer, given in RFC 1321, §3.3 as the bytes of each word, low-order byte first:
A = 01 23 45 67, B = 89 ab cd ef, C = fe dc ba 98, D = 76 54 32 10
-/
def Buffer.initial : Buffer where
  A := 0x67452301
  B := 0xefcdab89
  C := 0x98badcfe
  D := 0x10325476

end Standards.RFC.MD5
