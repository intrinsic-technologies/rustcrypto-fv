import Standards.NIST.GCM.Strings

/-!
# SP 800-38D §6.2: the incrementing function

The `s`-bit incrementing function `inc_s` of NIST SP 800-38D, §6.2, and the two §6.1 functions
it uses that `Standards.NIST.GCM.Strings` does not define: the integer-to-string function
`[x]_s` and the string-to-integer function `int`. A bit string of length `n` is a
`Vector Bool n`, its left-most bit first, as in `Standards.NIST.GCM.Strings`.

Source: https://nvlpubs.nist.gov/nistpubs/Legacy/SP/nistspecialpublication800-38d.pdf
-/

namespace Standards.NIST.GCM

/--
`[x]_s`, the binary representation of `x` as a string of `s` bits, least significant bit on the
right (SP 800-38D, §6.1); the document requires `x < 2^s`, and for larger `x` this is the
representation of `x mod 2^s`
-/
def integerToString (s x : Nat) : Vector Bool s :=
  Vector.ofFn fun i => x.testBit (s - 1 - i.val)

/--
`int(X)`, the integer whose binary representation is `X`, left-most bit most significant
(SP 800-38D, §6.1); the document defines it for non-empty strings, and the empty string gives 0
-/
def int (X : Vector Bool n) : Nat :=
  X.foldl (fun x bit => 2 * x + bit.toNat) 0

/--
`inc_s(X) = MSB_{len(X)-s}(X) || [int(LSB_s(X)) + 1 mod 2^s]_s`: the right-most `s` bits of `X`
incremented modulo `2^s`, the other bits unchanged (SP 800-38D, §6.2)
-/
def inc (s : Nat) (X : Vector Bool (k + s)) : Vector Bool (k + s) :=
  MSB k X ++ integerToString s ((int (LSB s X) + 1) % 2 ^ s)

end Standards.NIST.GCM
