/-!
# SP 800-38D §6.1: bit strings

The operations on bit strings that Algorithms 1 and 2 use (NIST SP 800-38D, §6.1): the string of
`s` zero bits, exclusive-OR, the `s` least and most significant bits, and the right shift. A bit
string of length `n` is a `Vector Bool n`, its left-most bit first; concatenation is `++` and the
length is the type's `n`.

SP 800-38D does not state how a byte string is a bit string; §5.2.1.1 only requires the lengths
of GCM's inputs to be multiples of 8 "so that these values are byte strings". `bitsOfBytes` and
`bytesOfBits` take FIPS 197-upd1, §3.3 (Eqs. 3.1–3.5, with the bit order of §3.2), for the AES
block cipher GCM is used with: byte j holds bits 8j to 8j + 7, the first of them its most
significant bit (https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.197-upd1.pdf).

Source: https://nvlpubs.nist.gov/nistpubs/Legacy/SP/nistspecialpublication800-38d.pdf
-/

namespace Standards.NIST.GCM

/-- `0^s`, the string of `s` zero bits (SP 800-38D, §6.1) -/
def zeros (s : Nat) : Vector Bool s := Vector.replicate s false

/-- `X ⊕ Y`, the bitwise addition modulo 2 of two strings of equal length (SP 800-38D, §6.1) -/
def xor (X Y : Vector Bool n) : Vector Bool n := Vector.zipWith Bool.xor X Y

/-- `LSB_s(X)`, the `s` right-most bits of a string of at least `s` bits (SP 800-38D, §6.1) -/
def LSB (s : Nat) (X : Vector Bool (k + s)) : Vector Bool s := Vector.ofFn fun i => X[k + i.val]

/-- `MSB_s(X)`, the `s` left-most bits of a string of at least `s` bits (SP 800-38D, §6.1) -/
def MSB (s : Nat) (X : Vector Bool (s + k)) : Vector Bool s := Vector.ofFn fun i => X[i.val]

/-- `X >> 1 = MSB_len(X)(0 || X)`, the single right shift (SP 800-38D, §6.1) -/
def rightShift (X : Vector Bool n) : Vector Bool n :=
  MSB n ((#v[false] ++ X).cast (Nat.add_comm 1 n))

/--
The bit string of `k` bytes: byte j gives bits 8j to 8j + 7, most significant bit first
(FIPS 197-upd1, §3.3, Eqs. 3.1–3.2)
-/
def bitsOfBytes (bytes : Vector UInt8 k) : Vector Bool (8 * k) :=
  Vector.ofFn fun i => (bytes[i.val / 8]'(by omega)).toNat.testBit (7 - i.val % 8)

/--
The `k` bytes of a bit string of length `8k`: byte j is bits 8j to 8j + 7, most significant bit
first (FIPS 197-upd1, §3.3, Eqs. 3.1–3.2)
-/
def bytesOfBits (bits : Vector Bool (8 * k)) : Vector UInt8 k :=
  Vector.ofFn fun j => ((List.finRange 8).foldl (fun byte b =>
    2 * byte + (bits[8 * j.val + b.val]'(by omega)).toNat) 0).toUInt8

end Standards.NIST.GCM
