/-!
# ChaCha20

The ChaCha20 stream cipher of RFC 8439, §§2.1–2.4: the quarter round on four 32-bit words
(`quarterRound`) and on four words of the state (`qround`), the state set up from a 256-bit key, a
32-bit block counter and a 96-bit nonce (`initialState`), `inner_block`, the block function
`chacha20_block` with its serialization, and `chacha20_encrypt` of a plaintext of any length, the
empty plaintext included, from any initial counter. Words are `UInt32`, so `+` is addition modulo
2^32 as §2.1 states.

`chacha20_encrypt` follows §2.4.1's pseudocode with two verified errata: 5989 replaces the printed
`encrypted_message += ...` with `|=`, concatenation; 7880 ends the slice of the last, partial block
at `(len(plaintext)%64)-1`, since the RFC's ranges are inclusive. `counter+j` is not said to wrap;
here it is the 32-bit sum, continuing at 0 after 2^32 - 1. §2.8 limits a single invocation to
2^32 - 1 blocks, below the first wrap from an initial counter of 1.

Not in the RFC: `chachaState` and `chachaBlock` take words 12–15 directly, and `chachaEncrypt` a
block counter of `counterWords` 32-bit words, taken modulo 2^(32 · `counterWords`), followed by
the nonce (`counterNonceWords`), so that the original layout of a 64-bit nonce and a 64-bit block
count (§2.3) is an instance of the same block function. RFC 8439's layout is `counterWords = 1`, on
which `initialState`, `chacha20Block` and `chacha20Encrypt` are defined; the original is
`counterWords = 2`; other values follow no document. The 128-bit keys and the 8- and 12-round
variants that §2.3 calls out of scope are not defined.

Errata: https://www.rfc-editor.org/errata/eid5989, https://www.rfc-editor.org/errata/eid7880

Source: https://www.rfc-editor.org/rfc/rfc8439.html
-/

namespace Standards.RFC.ChaCha20Poly1305

/--
`x <<< n`: the `n`-bit left roll of a 32-bit word, towards the high bits (RFC 8439, §2.1); a roll
by `n` equals a roll by `n % 32`
-/
def leftRoll (x : UInt32) (n : Nat) : UInt32 :=
  let k := n % 32
  (x <<< k.toUInt32) ||| (x >>> (32 - k).toUInt32)

/--
The ChaCha quarter round on four 32-bit words `a`, `b`, `c`, `d`, in the C-like notation of RFC
8439, §2.1:

1. `a += b; d ^= a; d <<<= 16;`
2. `c += d; b ^= c; b <<<= 12;`
3. `a += b; d ^= a; d <<<= 8;`
4. `c += d; b ^= c; b <<<= 7;`
-/
def quarterRound (a b c d : UInt32) : UInt32 × UInt32 × UInt32 × UInt32 := Id.run do
  let mut a := a
  let mut b := b
  let mut c := c
  let mut d := d
  a := a + b; d := d ^^^ a; d := leftRoll d 16
  c := c + d; b := b ^^^ c; b := leftRoll b 12
  a := a + b; d := d ^^^ a; d := leftRoll d 8
  c := c + d; b := b ^^^ c; b := leftRoll b 7
  return (a, b, c, d)

/--
`Qround(state, x, y, z, w)`, written `QUARTERROUND(x, y, z, w)` in the text: the quarter round on
the words at indices `x`, `y`, `z` and `w` of the ChaCha state, leaving the others alone (RFC 8439,
§2.2)
-/
def qround (state : Vector UInt32 16) (x y z w : Fin 16) : Vector UInt32 16 :=
  let (a, b, c, d) := quarterRound state[x] state[y] state[z] state[w]
  ((((state.set x a).set y b).set z c).set w d)

/--
`inner_block(state)`: a column round, quarter rounds 1–4, then a diagonal round, quarter rounds
5–8 (RFC 8439, §§2.3 and 2.3.1)
-/
def innerBlock (state : Vector UInt32 16) : Vector UInt32 16 :=
  let state := qround state 0 4 8 12
  let state := qround state 1 5 9 13
  let state := qround state 2 6 10 14
  let state := qround state 3 7 11 15
  let state := qround state 0 5 10 15
  let state := qround state 1 6 11 12
  let state := qround state 2 7 8 13
  qround state 3 4 9 14

/-- The 32-bit word in four bytes read in little-endian order (RFC 8439, §2.3) -/
def littleEndianWord (b₀ b₁ b₂ b₃ : UInt8) : UInt32 :=
  b₀.toUInt32 ||| (b₁.toUInt32 <<< 8) ||| (b₂.toUInt32 <<< 16) ||| (b₃.toUInt32 <<< 24)

/--
The ChaCha state `constants | key | words` (RFC 8439, §2.3), with the four words 12–15, which
hold the block counter and the nonce, as given:
- words 0–3: the constants `0x61707865`, `0x3320646e`, `0x79622d32`, `0x6b206574`;
- words 4–11: the key read in little-endian order in 4-byte chunks;
- words 12–15: `words`, in order.
-/
def chachaState (key : Vector UInt8 32) (words : Vector UInt32 4) : Vector UInt32 16 :=
  let keyWord (i : Nat) :=
    littleEndianWord key[4 * i]! key[4 * i + 1]! key[4 * i + 2]! key[4 * i + 3]!
  #v[0x61707865, 0x3320646e, 0x79622d32, 0x6b206574,
    keyWord 0, keyWord 1, keyWord 2, keyWord 3, keyWord 4, keyWord 5, keyWord 6, keyWord 7,
    words[0], words[1], words[2], words[3]]

/--
Words 12–15 of the state from a block counter of `counterWords` 32-bit words and a nonce of the
remaining `16 - 4 * counterWords` bytes: the counter modulo 2^(32 · `counterWords`), least
significant word first, then the nonce read in little-endian order in 4-byte chunks (above 4
counter words, only the counter's low 128 bits and no nonce). With
`counterWords = 1` this is RFC 8439's word 12 and words 13–15 (§2.3); with `counterWords = 2` the
original layout of a 64-bit counter and a 64-bit nonce. The general form is not in the RFC.
-/
def counterNonceWords (counterWords counter : Nat) (nonce : Vector UInt8 (16 - 4 * counterWords)) :
    Vector UInt32 4 :=
  Vector.ofFn fun i =>
    if i.val < counterWords then (counter >>> (32 * i.val)).toUInt32
    else
      let k := 4 * (i.val - counterWords)
      littleEndianWord nonce[k]! nonce[k + 1]! nonce[k + 2]! nonce[k + 3]!

/--
The ChaCha20 state `constants | key | counter | nonce` (RFC 8439, §2.3):
- words 0–3: the constants `0x61707865`, `0x3320646e`, `0x79622d32`, `0x6b206574`;
- words 4–11: the key read in little-endian order in 4-byte chunks;
- word 12: the block counter;
- words 13–15: the nonce read the same way, its first 32 bits in word 13.
-/
def initialState (key : Vector UInt8 32) (counter : UInt32) (nonce : Vector UInt8 12) :
    Vector UInt32 16 :=
  chachaState key (counterNonceWords 1 counter.toNat nonce)

/--
`serialize(state)`: the words one by one, each in little-endian order, as 64 bytes (RFC 8439,
§2.3)
-/
def serialize (state : Vector UInt32 16) : Vector UInt8 64 :=
  Vector.ofFn fun i => (state[i.val / 4] >>> (8 * (i.val % 4)).toUInt32).toUInt8

/--
The ChaCha20 block function on the key and the four words 12–15 of the state (RFC 8439, §2.3.1,
with `chachaState` in place of the state setup of step 1)

1. `state = chachaState key words`, and `initial_state = state`.
2. For `i = 1` upto `10`: `inner_block(state)`.
3. `state += initial_state`, word by word modulo 2^32.
4. Return `serialize(state)`.
-/
def chachaBlock (key : Vector UInt8 32) (words : Vector UInt32 4) : Vector UInt8 64 := Id.run do
  let mut state := chachaState key words
  let initialState := state
  for _ in [1:11] do
    state := innerBlock state
  state := Vector.ofFn fun i => state[i] + initialState[i]
  return serialize state

/--
`chacha20_block(key, counter, nonce)` (RFC 8439, §2.3.1)

Input: a 256-bit key, a 32-bit block counter and a 96-bit nonce
Output: 64 bytes

1. `state = constants | key | counter | nonce`, and `initial_state = state`.
2. For `i = 1` upto `10`: `inner_block(state)`.
3. `state += initial_state`, word by word modulo 2^32.
4. Return `serialize(state)`.

This is `chachaBlock` on the words of `initialState`.
-/
def chacha20Block (key : Vector UInt8 32) (counter : UInt32) (nonce : Vector UInt8 12) :
    Vector UInt8 64 :=
  chachaBlock key (counterNonceWords 1 counter.toNat nonce)

/--
ChaCha20 encryption with a block counter of `counterWords` 32-bit words (RFC 8439, §2.4.1, with
verified Errata 5989 and 7880, on `counterNonceWords` in place of the 32-bit counter and 96-bit
nonce)

1. For `j = 0` upto `floor(len(plaintext)/64)-1`: `key_stream = chachaBlock(key,
   counterNonceWords(counterWords, counter+j, nonce))`, and the 64-byte block
   `plaintext[(j*64)..(j*64+63)]` XOR `key_stream` is appended.
2. If `len(plaintext) % 64` is not zero, then with `j = floor(len(plaintext)/64)` the remaining
   bytes XOR the start of the block for `counter+j` are appended.

`counter+j` is taken modulo 2^(32 · `counterWords`), so the counter wraps at the width of its
words: 2^32 for RFC 8439 and 2^64 for the original layout. Decryption is the same function applied
to the ciphertext (§2.4).
-/
def chachaEncrypt (counterWords : Nat) (key : Vector UInt8 32) (counter : Nat)
    (nonce : Vector UInt8 (16 - 4 * counterWords)) (plaintext : ByteArray) : ByteArray := Id.run do
  let xorBytes (block : ByteArray) (keyStream : Vector UInt8 64) : ByteArray :=
    ⟨Array.ofFn fun i : Fin block.size => block[i] ^^^ keyStream[i.val]!⟩
  let keyStream (j : Nat) : Vector UInt8 64 :=
    chachaBlock key (counterNonceWords counterWords ((counter + j) % 2 ^ (32 * counterWords)) nonce)
  let mut encryptedMessage := ByteArray.empty
  for j in [0:plaintext.size / 64] do
    let block := plaintext.extract (j * 64) (j * 64 + 64)
    encryptedMessage := encryptedMessage ++ xorBytes block (keyStream j)
  if plaintext.size % 64 ≠ 0 then
    let j := plaintext.size / 64
    let block := plaintext.extract (j * 64) plaintext.size
    encryptedMessage := encryptedMessage ++ xorBytes block (keyStream j)
  return encryptedMessage

/--
`chacha20_encrypt(key, counter, nonce, plaintext)` (RFC 8439, §2.4.1, with verified Errata 5989
and 7880)

Input: a 256-bit key, a 32-bit initial counter, a 96-bit nonce and a plaintext of any length
Output: the ciphertext, of the plaintext's length

1. For `j = 0` upto `floor(len(plaintext)/64)-1`: `key_stream = chacha20_block(key, counter+j,
   nonce)`, and the 64-byte block `plaintext[(j*64)..(j*64+63)]` XOR `key_stream` is appended.
2. If `len(plaintext) % 64` is not zero, then with `j = floor(len(plaintext)/64)` the remaining
   bytes XOR the start of `chacha20_block(key, counter+j, nonce)` are appended.

`counter+j` is the 32-bit sum. Decryption is the same function applied to the ciphertext (§2.4).
This is `chachaEncrypt` with one counter word.
-/
def chacha20Encrypt (key : Vector UInt8 32) (counter : UInt32) (nonce : Vector UInt8 12)
    (plaintext : ByteArray) : ByteArray :=
  chachaEncrypt 1 key counter.toNat nonce plaintext

end Standards.RFC.ChaCha20Poly1305
