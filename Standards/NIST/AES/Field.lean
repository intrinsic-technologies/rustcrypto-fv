/-!
# FIPS 197-upd1 §4: arithmetic on bytes

Bytes are elements of GF(2⁸) with the reduction polynomial m(x) = x⁸ + x⁴ + x³ + x + 1 of
FIPS 197-upd1 §4.2, Eq. (4.3); bit `i` of a `UInt8` is the bit bᵢ of §3.2, the coefficient of xⁱ
(§4, Eq. (4.1)).
FIPS 197 in the docstrings is FIPS 197-upd1.

Source: https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.197-upd1.pdf
-/

namespace Standards.NIST.AES

/-- XTIMES, FIPS 197 §4.2, Eq. (4.5): multiplication by x, reduced modulo m(x) -/
def xtimes (b : UInt8) : UInt8 :=
  (b <<< 1) ^^^ (if b &&& 0x80 == 0 then 0 else 0x1b)

/--
Multiplication in GF(2⁸), FIPS 197 §4.2, Eq. (4.4): the sum of `b • xⁱ` over the bits `i` set in
`c`, each `b • xⁱ` obtained by `i` applications of XTIMES, as in the worked example of
Eqs. (4.6)–(4.7)
-/
def mul (b c : UInt8) : UInt8 :=
  ((List.range 8).foldl (fun (acc : UInt8 × UInt8) i =>
    (acc.1 ^^^ (if (c >>> i.toUInt8) &&& 1 == 1 then acc.2 else 0), xtimes acc.2)) (0, b)).1

/-- `b^n` in GF(2⁸), by repeated multiplication -/
def pow (b : UInt8) (n : Nat) : UInt8 :=
  (List.range n).foldl (fun acc _ => mul acc b) 1

/--
Multiplicative inverse, FIPS 197 §4.4, Eq. (4.11): b⁻¹ = b²⁵⁴ for nonzero b; §5.1.1, Eq. (5.2),
maps 00 to itself, which b²⁵⁴ also does
-/
def inverse (b : UInt8) : UInt8 := pow b 254

end Standards.NIST.AES
