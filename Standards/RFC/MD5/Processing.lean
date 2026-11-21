import Standards.RFC.MD5.Buffer

/-!
# Processing the message in 16-word blocks

Step 4 of RFC 1321, §3.4: the auxiliary functions F, G, H, and I, the sine table T, the four
rounds of 16 operations on a block, and the loop over the blocks of a message. Words are added
modulo 2^32. The RFC's `X <<< s`, the rotation of X left by s bits (§2), is `X.rotateLeft s`
here; Lean's `<<<` on `BitVec` is a shift, and the docstrings use `<<<` only in the RFC's sense.

Source: https://www.rfc-editor.org/rfc/rfc1321
-/

namespace Standards.RFC.MD5

/-- Auxiliary function of round 1: `F(X,Y,Z) = XY v not(X) Z` (RFC 1321, §3.4) -/
def F (X Y Z : BitVec 32) : BitVec 32 := (X &&& Y) ||| (~~~X &&& Z)

/-- Auxiliary function of round 2: `G(X,Y,Z) = XZ v Y not(Z)` (RFC 1321, §3.4) -/
def G (X Y Z : BitVec 32) : BitVec 32 := (X &&& Z) ||| (Y &&& ~~~Z)

/-- Auxiliary function of round 3: `H(X,Y,Z) = X xor Y xor Z` (RFC 1321, §3.4) -/
def H (X Y Z : BitVec 32) : BitVec 32 := X ^^^ Y ^^^ Z

/-- Auxiliary function of round 4: `I(X,Y,Z) = Y xor (X v not(Z))` (RFC 1321, §3.4) -/
def I (X Y Z : BitVec 32) : BitVec 32 := Y ^^^ (X ||| ~~~Z)

/--
The table T[1 ... 64], whose i-th element is the integer part of 4294967296 times abs(sin(i)),
i in radians, stored from index 0, so the RFC's T[i] is `T[i - 1]` (RFC 1321, §3.4 and
Appendix A.3). Appendix A.3 prints each constant in hexadecimal inside the FF, GG, HH and II
steps, without leading zeros: T[22], written `0x02441453` here, is printed `0x2441453`, and
T[44], written `0x04881d05` here, is printed `0x4881d05`
-/
def T : Vector (BitVec 32) 64 := #v[
  0xd76aa478, 0xe8c7b756, 0x242070db, 0xc1bdceee, 0xf57c0faf, 0x4787c62a,
  0xa8304613, 0xfd469501, 0x698098d8, 0x8b44f7af, 0xffff5bb1, 0x895cd7be,
  0x6b901122, 0xfd987193, 0xa679438e, 0x49b40821, 0xf61e2562, 0xc040b340,
  0x265e5a51, 0xe9b6c7aa, 0xd62f105d, 0x02441453, 0xd8a1e681, 0xe7d3fbc8,
  0x21e1cde6, 0xc33707d6, 0xf4d50d87, 0x455a14ed, 0xa9e3e905, 0xfcefa3f8,
  0x676f02d9, 0x8d2a4c8a, 0xfffa3942, 0x8771f681, 0x6d9d6122, 0xfde5380c,
  0xa4beea44, 0x4bdecfa9, 0xf6bb4b60, 0xbebfbc70, 0x289b7ec6, 0xeaa127fa,
  0xd4ef3085, 0x04881d05, 0xd9d4d039, 0xe6db99e5, 0x1fa27cf8, 0xc4ac5665,
  0xf4292244, 0x432aff97, 0xab9423a7, 0xfc93a039, 0x655b59c3, 0x8f0ccc92,
  0xffeff47d, 0x85845dd1, 0x6fa87e4f, 0xfe2ce6e0, 0xa3014314, 0x4e0811a1,
  0xf7537e82, 0xbd3af235, 0x2ad7d2bb, 0xeb86d391]

/--
The four rounds in order: each round's auxiliary function and the word index `k` and rotation
`s` of its 16 operations `[abcd k s i]`, which use T[1] to T[64] in order (RFC 1321, §3.4)
-/
def rounds : List ((BitVec 32 → BitVec 32 → BitVec 32 → BitVec 32) × List (Fin 16 × Nat)) := [
  (F, [(0, 7), (1, 12), (2, 17), (3, 22), (4, 7), (5, 12), (6, 17), (7, 22),
       (8, 7), (9, 12), (10, 17), (11, 22), (12, 7), (13, 12), (14, 17), (15, 22)]),
  (G, [(1, 5), (6, 9), (11, 14), (0, 20), (5, 5), (10, 9), (15, 14), (4, 20),
       (9, 5), (14, 9), (3, 14), (8, 20), (13, 5), (2, 9), (7, 14), (12, 20)]),
  (H, [(5, 4), (8, 11), (11, 16), (14, 23), (1, 4), (4, 11), (7, 16), (10, 23),
       (13, 4), (0, 11), (3, 16), (6, 23), (9, 4), (12, 11), (15, 16), (2, 23)]),
  (I, [(0, 6), (7, 10), (14, 15), (5, 21), (12, 6), (3, 10), (10, 15), (1, 21),
       (8, 6), (15, 10), (6, 15), (13, 21), (4, 6), (11, 10), (2, 15), (9, 21)])]

/--
Processing of one 16-word block X (RFC 1321, §3.4, body of the loop on i)

Input: the buffer (A, B, C, D) and the block X[0 ... 15]
Output: the buffer after the block

1. Save A as AA, B as BB, C as CC, and D as DD.
2. Do the 64 operations of `rounds`: the operation `[abcd k s i]` with auxiliary function f
   sets `a = b + ((a + f(b,c,d) + X[k] + T[i]) <<< s)` (RFC notation), and the registers named abcd
   move from ABCD to DABC, CDAB, BCDA, and back to ABCD in successive operations.
3. Set A = A + AA, B = B + BB, C = C + CC, and D = D + DD.
-/
def processBlock (buffer : Buffer) (X : Vector (BitVec 32) 16) : Buffer := Id.run do
  let operations := rounds.flatMap fun (f, operations) => operations.map fun (k, s) => (f, k, s)
  let mut a := buffer.A
  let mut b := buffer.B
  let mut c := buffer.C
  let mut d := buffer.D
  for ((f, k, s), t) in operations.zip T.toList do
    let updated := b + (a + f b c d + X[k] + t).rotateLeft s
    (a, b, c, d) := (d, updated, b, c)
  return ⟨buffer.A + a, buffer.B + b, buffer.C + c, buffer.D + d⟩

/--
Processing of the message words M[0 ... N-1] in 16-word blocks, starting from `buffer`
(RFC 1321, §3.4, the loop `For i = 0 to N/16-1`): block i is the words M[i*16 ... i*16+15].
Words after the last complete block are not read, which keeps the function total; the RFC, where
N is a multiple of 16, does not say this.
-/
def processBlocks (buffer : Buffer) (M : Array (BitVec 32)) : Buffer := Id.run do
  let mut buffer := buffer
  for i in [0:M.size / 16] do
    let X : Vector (BitVec 32) 16 := Vector.ofFn fun j => M.getD (i * 16 + j.val) 0
    buffer := processBlock buffer X
  return buffer

end Standards.RFC.MD5
